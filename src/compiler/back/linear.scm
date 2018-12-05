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

;;;; LAP linearizer
;;; package: (compiler lap-syntaxer linearizer)

(declare (usual-integrations))

(define (bblock-linearize-lap bblock queue-continuations!)
  (define (linearize-bblock bblock)
    (LAP ,@(linearize-bblock-1 bblock)
	 ,@(linearize-next bblock)))

  (define (linearize-bblock-1 bblock)
    (node-mark! bblock)
    (queue-continuations! bblock)
    (if (and (not (bblock-label bblock))
	     (let loop ((bblock bblock))
	       (or (node-previous>1? bblock)
		   (and (node-previous=1? bblock)
			(let ((previous (node-previous-first bblock)))
			  (and (sblock? previous)
			       (null? (bblock-instructions previous))
			       (loop previous)))))))
	(bblock-label! bblock))
    (let ((kernel
	   (lambda ()
	     (bblock-instructions bblock))))
      (if (bblock-label bblock)
	  (LAP ,@(lap:make-label-statement (bblock-label bblock)) ,@(kernel))
	  (kernel))))

  (define (linearize-next bblock)
    (if (sblock? bblock)
	(let ((next (find-next (snode-next bblock))))
	  (if next
	      (linearize-sblock-next next (bblock-label next))
	      (let ((bblock (sblock-continuation bblock)))
		(if (and bblock (not (node-marked? bblock)))
		    (linearize-bblock bblock)
		    (LAP)))))
	(linearize-pblock
	 bblock
	 (find-next (pnode-consequent bblock))
	 (find-next (pnode-alternative bblock)))))

  (define (linearize-sblock-next bblock label)
    (if (node-marked? bblock)
	(lap:make-unconditional-branch label)
	(linearize-bblock bblock)))

  (define (linearize-pblock pblock cn an)
    (if (node-marked? cn)
	(if (node-marked? an)
	    (backward-preference pblock cn an
	      (lambda (generator cn an)
		(LAP ,@(lap:comment '(BOTH BACKWARD))
		     ,@(generator (bblock-label cn))
		     ,@(lap:make-unconditional-branch (bblock-label an)))))
	    (LAP ,@(backward-or-fallthrough
		    pblock
		    'CONSEQUENT
		    (bblock-label cn)
		    (pblock-consequent-lap-generator pblock)
		    (pblock-alternative-lap-generator pblock))
		 ,@(linearize-bblock an)))
	(if (node-marked? an)
	    (LAP ,@(backward-or-fallthrough
		    pblock
		    'ALTERNATIVE
		    (bblock-label an)
		    (pblock-alternative-lap-generator pblock)
		    (pblock-consequent-lap-generator pblock))
		 ,@(linearize-bblock cn))
	    (linearize-pblock-1 pblock cn an))))

  (define (linearize-pblock-1 pblock cn an)
    (let ((finish
	   (lambda (generator cn an)
	     (let ((clabel (bblock-label! cn))
		   (alternative (linearize-bblock an)))
	       (LAP ,@(lap:comment '(FORWARD OR FALLTHROUGH))
		    ,@(generator clabel)
		    ,@alternative
		    ,@(if (node-marked? cn)
			  (LAP)
			  (linearize-bblock cn)))))))
      (let ((unspecial
	     (lambda ()
	       (forward-preference pblock cn an finish)))
	    (diamond
	     (lambda ()
	       (let ((jlabel (generate-label)))
		 (forward-preference pblock cn an
		   (lambda (generator cn an)
		     (let ((clabel (bblock-label! cn)))
		       (let ((consequent (linearize-bblock-1 cn))
			     (alternative (linearize-bblock-1 an)))
			 (LAP ,@(lap:comment '(DIAMOND))
			      ,@(generator clabel)
			      ,@alternative
			      ,@(lap:make-unconditional-branch jlabel)
			      ,@consequent
			      ,@(lap:make-label-statement jlabel)
			      ,@(linearize-next cn))))))))))
	(let ((consequent-first
	       (lambda ()
		 (if (pnode/preferred-branch pblock)
		     (unspecial)
		     (LAP ,@(lap:comment '(UNPREDICTED CONSEQUENT FIRST))
			  ,@(finish (pblock-alternative-lap-generator pblock)
				    an
				    cn)))))
	      (alternative-first
	       (lambda ()
		 (if (pnode/preferred-branch pblock)
		     (unspecial)
		     (LAP ,@(lap:comment '(UNPREDICTED ALTERNATIVE FIRST))
			  ,@(finish (pblock-consequent-lap-generator pblock)
				    cn
				    an))))))
	  (cond ((eq? cn an)
		 ;;(warn "bblock-linearize-lap: Identical branches" pblock)
		 (unspecial))
		((sblock? cn)
		 (let ((cnn (find-next (snode-next cn))))
		   (cond ((eq? cnn an)
			  (consequent-first))
			 ((sblock? an)
			  (let ((ann (find-next (snode-next an))))
			    (cond ((eq? ann cn)
				   (alternative-first))
				  ((not cnn)
				   (if ann
				       (consequent-first)
				       (if (null? (bblock-continuations cn))
					   (if (null? (bblock-continuations an))
					       (unspecial)
					       (consequent-first))
					   (if (null? (bblock-continuations an))
					       (alternative-first)
					       (unspecial)))))
				  ((not ann)
				   (alternative-first))
				  ((eq? cnn ann)
				   (diamond))
				  (else
				   (unspecial)))))
			 ((not cnn)
			  (consequent-first))
			 (else
			  (unspecial)))))
		((and (sblock? an)
		      (let ((ann (find-next (snode-next an))))
			(or (not ann)
			    (eq? ann cn))))
		 (alternative-first))
		(else
		 (unspecial)))))))

  ;; We are going to either branch to a preceding label, or continue
  ;; forward.  If backward branches are statically predicted not taken,
  ;; as on modern x86 and arm CPUs (2018) and probably others, then use
  ;; a backward branch if we predict it will be taken or have no
  ;; prediction, and use a forward branch if we predict it will be not
  ;; taken.  If, on the other hand, merely taking a branch is costly,
  ;; as in the SVM back end, or if we are deferring to a C compiler,
  ;; then just issue a backward branch.
  ;;
  ;; If we ever add support for CPUs like powerpc, we should perhaps
  ;; add a parameter to the machine-dependent branch generation to
  ;; include branch hints in the instruction stream.

  (define (backward-or-fallthrough pblock sense label backward forward)
    (LAP ,@(lap:comment '(BACKWARD OR FALLTHROUGH))
	 ,@(let ((preference (pnode/preferred-branch pblock)))
	     (if (or (not prefer-backward-branches?)
		     (not preference)
		     (eq? preference sense))
		 (LAP ,@(if (eq? preference sense)
			    (lap:comment '(PREDICT TAKEN BACKWARD))
			    (lap:comment '(UNPREDICTED)))
		      ,@(backward label))
		 (LAP ,@(lap:comment '(PREDICT NOT TAKEN BACKWARD VIA FORWARD))
		      ,@(backward-via-forward label forward))))))

  (define (backward-via-forward label forward)
    (let* ((label0 (generate-label))
	   (label1 (generate-label))
	   (label2 (generate-label)))
      (LAP ,@(lap:make-unconditional-branch label1)
	   (LABEL ,label0)
	   ,@(lap:make-unconditional-branch label2)
	   (LABEL ,label1)
	   ,@(forward label0)
	   ,@(lap:make-unconditional-branch label)
	   (LABEL ,label2))))

  ;; We are going to make a backward branch to one or the other of two
  ;; blocks.  Pick one to branch to as the `consequent' and provide its
  ;; generator, and one to fall through to as the alternative, so that
  ;; the preferred branch uses the cheaper path.

  (define (backward-preference pblock cn an finish)
    (if prefer-backward-branches?
	;; If backward branches are statically predicted not taken,
	;; supply the preferred destination as the branch.
	(if (eq? 'CONSEQUENT (pnode/preferred-branch pblock))
	    (LAP ,@(lap:comment '(PREDICT TAKEN BACKWARD CONSEQUENT))
		 ,@(finish (pblock-consequent-lap-generator pblock) cn an))
	    (LAP ,@(if (pnode/preferred-branch pblock)
		       (lap:comment '(PREDICT TAKEN BACKWARD ALTERNATIVE))
		       (lap:comment '(UNPREDICTED)))
		 ,@(finish (pblock-alternative-lap-generator pblock) an cn)))
	;; If fallthroughs are cheaper than taken branches, supply the
	;; preferred destination as the fallthrough.
	(if (eq? 'CONSEQUENT (pnode/preferred-branch pblock))
	    (LAP ,@(lap:comment '(PREDICT NOT TAKEN BACKWARD ALTERNATIVE))
		 ,@(finish (pblock-alternative-lap-generator pblock) an cn))
	    (LAP ,@(if (pnode/preferred-branch pblock)
		       (lap:comment '(PREDICT NOT TAKEN BACKWARD CONSEQUENT))
		       (lap:comment '(UNPREDICTED)))
		 ,@(finish (pblock-consequent-lap-generator pblock) cn an)))))

  ;; We are going to make a forward branch to one or the other of two
  ;; blocks.  Pick one to branch to as the `consequent' and provide its
  ;; generator, and one to fall through to as the alternative, so that
  ;; the preferred branch uses the cheaper path.

  (define (forward-preference pblock cn an finish)
    ;; Whether forward branches are statically predicted not-taken, or
    ;; whether taken branches are costlier than fallthroughs, supply
    ;; the preferred destination as the fallthrough.
    (if (eq? 'CONSEQUENT (pnode/preferred-branch pblock))
	(LAP ,@(lap:comment '(PREDICT NOT TAKEN FORWARD ALTERNATIVE))
	     ,@(finish (pblock-alternative-lap-generator pblock) an cn))
	(LAP ,@(if (pnode/preferred-branch pblock)
		   (lap:comment '(PREDICT NOT TAKEN FORWARD CONSEQUENT))
		   (lap:comment '(UNPREDICTED)))
	     ,@(finish (pblock-consequent-lap-generator pblock) cn an))))

  (define (find-next bblock)
    (let loop ((bblock bblock) (previous false))
      (cond ((not bblock)
	     previous)
	    ((and (sblock? bblock)
		  (null? (bblock-instructions bblock)))
	     (loop (snode-next bblock) bblock))
	    (else
	     bblock))))

  (linearize-bblock bblock))

(define-integrable (set-current-branches! consequent alternative)
  (set-pblock-consequent-lap-generator! *current-bblock* consequent)
  (set-pblock-alternative-lap-generator! *current-bblock* alternative))

(define *end-of-block-code*)

(define-structure (extra-code-block
		   (conc-name extra-code-block/)
		   (constructor extra-code-block/make
				(name constraint xtra)))
  (name false read-only true)
  (constraint false read-only true)
  (code (LAP) read-only false)
  (xtra false read-only false))

(define linearize-lap
  (make-linearizer bblock-linearize-lap
    (lambda () (LAP))
    (lambda (x y) (LAP ,@x ,@y))
    (lambda (linearized-lap)
      (let ((end-code *end-of-block-code*))
	(set! *end-of-block-code* '())
	(LAP ,@linearized-lap
	     ,@(let process ((end-code end-code))
		 (if (null? end-code)
		     (LAP)
		     (LAP ,@(extra-code-block/code (car end-code))
			  ,@(process (cdr end-code))))))))))

(define (find-extra-code-block name)
  (let loop ((end-code *end-of-block-code*))
    (cond ((null? end-code) false)
	  ((eq? name (extra-code-block/name (car end-code)))
	   (car end-code))
	  (else
	   (loop (cdr end-code))))))

(define (declare-extra-code-block! name constraint xtra)
  (if (find-extra-code-block name)
      (error "declare-extra-code-block!: Multiply defined block"
	     name)
      (let ((new (extra-code-block/make name constraint xtra))
	    (all *end-of-block-code*))

	(define (constraint-violation new old)
	  (error "declare-extra-code-block!: Inconsistent constraints"
		 new old))

	(case constraint
	  ((FIRST)
	   (if (and (not (null? all))
		    (eq? 'FIRST
			 (extra-code-block/constraint (car all))))
	       (constraint-violation new (car all)))
	   (set! *end-of-block-code* (cons new all)))
	  ((ANYWHERE)
	   (if (or (null? all)
		   (not (eq? 'FIRST
			     (extra-code-block/constraint (car all)))))
	       (set! *end-of-block-code* (cons new all))
	       (set-cdr! all (cons new (cdr all)))))
	  ((LAST)
	   (if (null? all)
	       (set! *end-of-block-code* (list new))
	       (let* ((lp (last-pair all))
		      (old (car lp)))
		 (if (eq? 'LAST (extra-code-block/constraint old))
		     (constraint-violation new old))
		 (set-cdr! lp (cons new '())))))
	  (else
	   (error "declare-extra-code-block!: Unknown constraint"
		  constraint)))
	new)))

(define (add-extra-code! block new-code)
  (set-extra-code-block/code!
   block
   (LAP ,@(extra-code-block/code block)
	,@new-code)))

(define (add-end-of-block-code! code-thunk)
  (add-extra-code!
   (or (find-extra-code-block 'END-OF-BLOCK)
       (declare-extra-code-block! 'END-OF-BLOCK 'ANYWHERE false))
   (code-thunk)))