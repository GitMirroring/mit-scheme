#| -*-Scheme-*-

Copyright (C) 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994,
    1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005,
    2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016,
    2017, 2018 Massachusetts Institute of Technology

This file is part of MIT/GNU Scheme.

MIT/GNU Scheme is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or (at
your option) any later version.

MIT/GNU Scheme is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with MIT/GNU Scheme; if not, write to the Free Software
Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301,
USA.

|#

;;;; Finish cross-compilation process

;;; This program takes the output of the cross compiler (.moc files)
;;; and converts it into its final form.  It must be run on the target
;;; machine.  It can be loaded and run without the rest of the
;;; compiler.

(declare (usual-integrations))

(load-option 'COMPRESS)                        ; XXX ugh

(define (finish-cross-compilation:directory directory #!optional force?)
  (let ((force? (if (default-object? force?) #f force?)))
    (let loop ((directory directory))
      (for-each (lambda (pathname)
		  (cond ((file-directory? pathname)
			 (if (not (let ((ns (file-namestring pathname)))
				    (or (string=? ns ".")
					(string=? ns ".."))))
			     (loop pathname)))
			((let ((t (pathname-type pathname)))
			   (and (string? t)
				(string=? t "fni")))
			 (finish-cross-compilation:info-file pathname force?))
			((let ((t (pathname-type pathname)))
			   (and (string? t)
				(string=? t "moc")))
			 (finish-cross-compilation:file pathname force?))))
		(directory-read (pathname-as-directory directory))))))

(define (finish-cross-compilation:files directory #!optional force?)
  (let ((force? (if (default-object? force?) #f force?)))
    (let loop ((directory directory))
      (for-each (lambda (pathname)
                 (cond ((file-directory? pathname)
                        (if (not (let ((ns (file-namestring pathname)))
                                   (or (string=? ns ".")
                                       (string=? ns ".."))))
                            (loop pathname)))
                       ((let ((t (pathname-type pathname)))
                          (and (string? t)
                               (string=? t "moc")))
                        (finish-cross-compilation:file pathname force?))))
               (directory-read (pathname-as-directory directory))))))

(define (finish-cross-compilation:info-files directory #!optional force?)
  (let ((force? (if (default-object? force?) #f force?)))
    (let loop ((directory directory))
      (for-each (lambda (pathname)
		  (cond ((file-directory? pathname)
			 (if (not (let ((ns (file-namestring pathname)))
				    (or (string=? ns ".")
					(string=? ns ".."))))
			     (loop pathname)))
			((let ((t (pathname-type pathname)))
			   (and (string? t)
				(string=? t "fni")))
			 (finish-cross-compilation:info-file pathname force?))))
		(directory-read (pathname-as-directory directory))))))

(define (finish-cross-compilation:info-file pathname #!optional force?)
  (let* ((input-file (pathname-default-type pathname "fni"))
	 (output-file (pathname-new-type input-file "bci")))
    (if (or (if (default-object? force?) #t force?)
	    (file-modification-time<? output-file input-file))
	(with-notification
	    (lambda (port)
	      (write-string "Compressing info: " port)
	      (write (enough-namestring input-file) port)
	      (write-string " => " port)
	      (write (enough-namestring output-file) port))
	    (lambda ()
	      (let ((inf (fasload input-file #t)))
		(call-with-temporary-filename
		  (lambda (temp)
		    (fasdump inf temp #t)
		    (compress temp output-file)))))))))

(define (finish-cross-compilation:file input-file #!optional force?)
  (let* ((input-file (pathname-default-type input-file "moc"))
	 (output-file (pathname-new-type input-file "com")))
    (if (or (if (default-object? force?) #t force?)
	    (file-modification-time<? output-file input-file))
	(with-notification
	    (lambda (port)
	      (write-string "Compiling file: " port)
	      (write (enough-namestring input-file) port)
	      (write-string " => " port)
	      (write (enough-namestring output-file) port))
	  (lambda ()
	    (fasdump (finish-cross-compilation:scode (fasload input-file #t))
		     output-file
		     #t))))))

(define (finish-cross-compilation:scode cross-compilation)
  (let ((compile-by-procedures? (vector-ref cross-compilation 0))
	(expression (cross-link-end (vector-ref cross-compilation 1)))
	(others (map cross-link-end (vector-ref cross-compilation 2))))
    (if (null? others)
	expression
	(scode/make-comment
	 ;; Keep in sync with "toplev.scm" and with "runtime/infstr.scm".
	 (vector
	  '|#[(runtime compiler-info)dbg-info-vector]|
	  (if compile-by-procedures?
	      'compiled-by-procedures
	      'compiled-as-unit)
	  (compiled-code-address->block expression)
	  (list->vector
	   (map (lambda (other)
		  (vector-ref other 2))
		others))
	  '()
	  '()
	  '())
	 expression))))

(define (cross-link-end object)
  (let ((code-vector (cc-vector/code-vector object)))
    (cross-link/process-code-vector
     (if (compiled-code-block? code-vector)
	 code-vector
	 (begin
	   (guarantee vector? code-vector #f)
	   (let ((new-code-vector
		  (cross-link/finish-assembly
		   (cc-code-block/bit-string code-vector)
		   (cc-code-block/objects code-vector)
		   (cc-code-block/object-width code-vector)
		   (cc-code-block/float-width code-vector)
		   (cc-code-block/float-alignment code-vector))))
	     (set-compiled-code-block/debugging-info!
	      new-code-vector
	      (cc-code-block/debugging-info code-vector))
	     new-code-vector)))
     object)))

(define (cross-link/process-code-vector code-vector cc-vector)
  (let ((bindings
	 (let ((label-bindings (cc-vector/label-bindings cc-vector)))
	   (map (lambda (label)
		  (cons
		   label
		   (let ((offset
			  (cdr (or (assq label label-bindings)
				   (error "Missing entry point" label)))))
		     (with-absolutely-no-interrupts
		       (lambda ()
			 ((ucode-primitive primitive-object-set-type)
			  (ucode-type compiled-entry)
			  (make-non-pointer-object
			   (+ offset
			      (object-datum code-vector)))))))))
		(cc-vector/entry-points cc-vector)))))
    (let ((label->expression
	   (lambda (label)
	     (cdr (or (assq label bindings)
		      (error "Label not defined as entry point:" label))))))
      (let ((expression (label->expression (cc-vector/entry-label cc-vector))))
	(for-each (lambda (entry)
		    (set-lambda-body! (car entry)
				      (label->expression (cdr entry))))
		  (cc-vector/ic-procedure-headers cc-vector))
	expression))))

(define (cross-link/finish-assembly code-block objects
				    scheme-object-width
				    float-width
				    float-alignment)
  ;; See layout diagram in assemble-objects in back/bittop.scm.
  (let* ((manifest-length 1)		;vector header
	 (manifest-nm-length 1)		;nmv header, at aligned address
	 (padding-length		;padding to align next address
	  (- (quotient float-alignment scheme-object-width)
	     manifest-nm-length))
	 (code-length		;XXX Should this round up?
	  (quotient (bit-string-length code-block) scheme-object-width))
	 (non-pointer-length (+ padding-length code-length))
	 ;; Offsets are for system-vector-ref, and start at the
	 ;; address after the manifest header.
	 (manifest-nm-offset 0)
	 (padding-offset (+ manifest-nm-offset manifest-nm-length))
	 (code-offset (+ padding-offset padding-length))
	 (objects-offset (+ code-offset code-length))
	 (total-length (+ objects-offset (length objects)))
	 (flo-length
	  (let ((flo-size (quotient float-width scheme-object-width)))
	    (quotient (+ total-length (- flo-size 1)) flo-size)))
	 (output-block
	  (object-new-type (ucode-type compiled-code-block)
			   (flo:vector-cons flo-length))))
    (with-absolutely-no-interrupts
      (lambda ()
	(let ((ob (object-new-type (ucode-type vector) output-block)))
	  (subvector-fill! ob objects-offset (system-vector-length ob) #f)
	  (vector-set! ob 0
		       ((ucode-primitive primitive-object-set-type)
			(ucode-type manifest-nm-vector)
			non-pointer-length)))))
    ;; write-bits! is relative to address of manifest.
    (write-bits! output-block
		 (* scheme-object-width (+ manifest-length code-offset))
		 code-block)
    ((ucode-primitive primitive-object-set! 3)
     output-block 0
     (object-new-type (ucode-type manifest-vector) total-length))
    (insert-objects! output-block objects objects-offset)
    (object-new-type (ucode-type compiled-code-block) output-block)))

(define (insert-objects! v objects where)
  (cond ((not (null? objects))
	 (system-vector-set! v where (cadar objects))
	 (insert-objects! v (cdr objects) (fix:+ where 1)))
	((not (fix:= where (system-vector-length v)))
	 (error "insert-objects!: object phase error" where))
	(else unspecific)))

(define-structure (cc-code-block (type vector)
				 (conc-name cc-code-block/))
  (debugging-info #f read-only #f)
  (bit-string #f read-only #t)
  (objects #f read-only #t)
  (object-width #f read-only #t)
  (float-width #f read-only #t)
  (float-alignment #f read-only #t))

(define-structure (cc-vector (type vector)
			     (constructor cc-vector/make)
			     (conc-name cc-vector/))
  (code-vector #f read-only #t)
  (entry-label #f read-only #t)
  (entry-points #f read-only #t)
  (label-bindings #f read-only #t)
  (ic-procedure-headers #f read-only #t))

(define-syntax ucode-primitive
  (sc-macro-transformer
   (lambda (form environment)
     environment
     (apply make-primitive-procedure (cdr form)))))

(define-syntax ucode-type
  (sc-macro-transformer
   (lambda (form environment)
     environment
     (apply microcode-type (cdr form)))))