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

;;;; LAP Optimizer for AMD x86-64
;;; package: (compiler lap-optimizer)

(declare (usual-integrations))

(define (optimize-linear-lap instructions)
  (rewrite-lap instructions))

;; i386 LAPOPT uses its own pattern matcher because we want to match
;; patterns while ignoring comments.
;;
;; XXX Factor this out into compiler/base or compiler/back.

(define (comment? thing)
  (and (pair? thing) (eq? (car thing) 'COMMENT)))

(define (match pat thing dict)		; -> #F or dictionary (alist)
  (if (pair? pat)
      (if (eq? (car pat) '?)
	  (cond ((assq (cadr pat) dict)
		 => (lambda (pair)
		      (and (equal? (cdr pair) thing)
			   dict)))
		(else (cons (cons (cadr pat) thing) dict)))
	  (and (pair? thing)
	       (let ((dict* (match (car pat) (car thing) dict)))
		 (and dict*
		      (match (cdr pat) (cdr thing) dict*)))))
      (and (eqv? pat thing)
	   dict)))

(define (match-sequence pats things dict comments success fail)
  ;; SUCCESS = (lambda (dict* comments* things-tail) ...)
  ;; FAIL =  (lambda () ...)

  (define (eat-comment)
    (match-sequence pats (cdr things) dict (cons (car things) comments)
		    success fail))

  (cond ((not (pair? pats))		; i.e. null
	 (if (and (pair? things)
		  (comment? (car things)))
	     (eat-comment)
	     (success dict comments things)))
	((not (pair? things))
	 (fail))
	((match (car pats) (car things) dict)
	 => (lambda (dict*)
	      (match-sequence (cdr pats) (cdr things) dict* comments
			      success fail)))
	((comment? (car things))
	 (eat-comment))
	(else (fail))))

(define-structure
    (rule)
  name					; used only for information
  pattern				; INSNs (in reverse order)
  predicate				; (lambda (dict) ...) -> bool
  constructor)				; (lambda (dict) ...) -> lap

(define *rules* (make-strong-eq-hash-table))


;; Rules are indexed by the last opcode in the pattern.

(define (define-lapopt name pattern predicate constructor)
  (let ((pattern (reverse pattern)))
    (let ((rule (make-rule name
			   pattern
			   (if ((access procedure? system-global-environment)
				predicate)
			       predicate
			       (lambda (dict) dict #T))
			   constructor)))
      (if (or (not (pair? pattern))
	      (not (pair? (car pattern))))
	  (error "Illegal LAPOPT pattern - must end with opcode"
		 (reverse pattern)))
      (let ((key (caar pattern)))
	(hash-table-set! *rules* key
			 (cons rule
			       (hash-table-ref/default *rules* key '()))))))
  name)

(define (find-rules instruction)
  (hash-table-ref/default *rules* (car instruction) '()))

;; Rules are tried in the reverse order in which they are defined.
;;
;; Rules are matched against the LAP from the bottom up.
;;
;; Once a rule has been applied, the rewritten LAP is matched again,
;; so a rule must rewrite to something different to avoid a loop.
;; (One way to ensure this is to always rewrite to fewer instructions.)

(define (rewrite-lap lap)
  (let loop ((unseen (reverse lap)) (finished '()))
    (if (null? unseen)
	finished
	(if (comment? (car unseen))
	    (loop (cdr unseen) (cons (car unseen) finished))
	    (let try-rules ((rules (find-rules (car unseen))))
	      (if (null? rules)
		  (loop (cdr unseen) (cons (car unseen) finished))
		  (let ((rule (car rules)))
		    (match-sequence
		     (rule-pattern rule)
		     unseen
		     '(("empty"))	; initial dict, distinct from #F and ()
		     '()		; initial comments
		     (lambda (dict comments unseen*)
		       (let ((dict (alist->dict dict)))
			 (if ((rule-predicate rule) dict)
			     (let ((rewritten
				    (cons
				     `(COMMENT (LAP-OPT ,(rule-name rule)))
				     (append comments
					     ((rule-constructor rule) dict)))))
			       (loop (append (reverse rewritten) unseen*)
				     finished))
			     (try-rules (cdr rules)))))
		     (lambda ()
		       (try-rules (cdr rules)))))))))))

;; The DICT passed to the rule predicate and action procedures is a
;; procedure mapping pattern names to their matched values.

(define (alist->dict dict)
  (lambda (symbol)
    (cond ((assq symbol dict) => cdr)
	  (else (error "Undefined lapopt pattern symbol" symbol dict)))))

(define-lapopt 'PUSH-EA-POP-REG->MOVE
  `((PUSH Q (? ea))
    (POP Q (R (? reg))))
  #F
  (lambda (dict)
    `((MOV Q (R ,(dict 'reg)) ,(dict 'ea)))))

(define-lapopt 'PUSH-REG-POP-EA->MOVE
  `((PUSH Q (R (? reg)))
    (POP Q (? ea)))
  #F
  (lambda (dict)
    `((MOV Q ,(dict 'ea) (R ,(dict 'reg))))))

(define-lapopt 'PUSH-POP->NOP
  `((PUSH Q (? ea))
    (POP Q (? ea)))
  #F
  (lambda (dict)
    dict
    `()))

(define-lapopt 'STACKWRITE-DROP->DROP-PUSH
  `((MOV Q (@RO 4 (? offset)) (R (? reg)))
    (ADD Q (R 4) (& (? offset))))
  (lambda (dict)
    ;; Shouldn't happen but just in case.
    (not (eqv? (dict 'reg) 4)))
  (lambda (dict)
    `((ADD Q (R 4) (& ,(+ 8 (dict 'offset))))
      (PUSH Q (R ,(dict 'reg))))))

;; This pattern occurs a lot in practice, but it suggests to me that
;; maybe CSE got confused or something.  Curious.

(define-lapopt 'STACKWRITE-DROP-RELOAD->DROP-PUSH
  `((MOV Q (@RO 4 (? offset)) (R (? reg)))
    (ADD Q (R 4) (& (? offset)))
    (MOV Q (R (? reg)) (@R 4)))
  (lambda (dict)
    ;; Shouldn't happen but just in case.
    (not (eqv? (dict 'reg) 4)))
  (lambda (dict)
    `((ADD Q (R 4) (& ,(+ 8 (dict 'offset))))
      (PUSH Q (R ,(dict 'reg))))))

;; The following rules recognize arithmetic followed by tag injection,
;; and fold the tag-injection into the arithmetic.  We can do this
;; because we know the bottom six bits of the fixnum are all 0.  This
;; is particularly crafty in the generic arithmetic case, as it does
;; not mess up the overflow detection.

(define fixnum-tag type-code:fixnum)

(define-lapopt 'FIXNUM-ADD-CONST-TAG
  `((ADD Q (R (? reg)) (& (? const)))
    (OR Q (R (? reg)) (&U ,fixnum-tag))
    (ROR Q (R (? reg)) (&U ,scheme-type-width)))
  #F
  (lambda (dict)
    `((ADD Q (R ,(dict 'reg)) (& ,(+ (dict 'const) fixnum-tag)))
      (ROR Q (R ,(dict 'reg)) (&U ,scheme-type-width)))))

(define-lapopt 'FIXNUM-SUB-CONST-TAG
  `((SUB Q (R (? reg)) (& (? const)))
    (OR Q (R (? reg)) (&U ,fixnum-tag))
    (ROR Q (R (? reg)) (&U ,scheme-type-width)))
  #F
  (lambda (dict)
    `((SUB Q (R ,(dict 'reg)) (& ,(- (dict 'const) fixnum-tag)))
      (ROR Q (R ,(dict 'reg)) (&U ,scheme-type-width)))))

;; FIXNUM-ADD-REG-TAG could be handled by a rule for
;;
;;      (FIXNUM->OBJECT
;;       (FIXNUM-2-ARGS PLUS-FIXNUM
;;                      (REGISTER (? source1))
;;                      (REGISTER (? source2)))),
;;
;; but getting all the registers right as binary-register-operation
;; does is too much of a pain to contemplate at the moment.

(define-lapopt 'FIXNUM-ADD-REG-TAG
  `((ADD Q (R (? reg)) (R (? reg-2)))
    (OR Q (R (? reg)) (&U ,fixnum-tag))
    (ROR Q (R (? reg)) (&U ,scheme-type-width)))
  #F
  (lambda (dict)
    `((LEA Q (R ,(dict 'reg)) (@ROI ,(dict 'reg) ,fixnum-tag ,(dict 'reg-2) 1))
      (ROR Q (R ,(dict 'reg)) (&U ,scheme-type-width)))))

(define-lapopt 'GENERIC-ADD-CONST-TAG
  `((ADD Q (R (? reg)) (& (? const)))
    (JO (@PCR (? label)))
    (OR Q (R (? reg)) (&U ,fixnum-tag))
    (ROR Q (R (? reg)) (&U ,scheme-type-width)))
  #F
  (lambda (dict)
    `((ADD Q (R ,(dict 'reg)) (& ,(+ (dict 'const) fixnum-tag)))
      (JO (@PCR ,(dict 'label)))
      (ROR Q (R ,(dict 'reg)) (&U ,scheme-type-width)))))

(define-lapopt 'GENERIC-SUB-CONST-TAG
  `((SUB Q (R (? reg)) (& (? const)))
    (JO (@PCR (? label)))
    (OR Q (R (? reg)) (&U ,fixnum-tag))
    (ROR Q (R (? reg)) (&U ,scheme-type-width)))
  #F
  (lambda (dict)
    `((SUB Q (R ,(dict 'reg)) (& ,(- (dict 'const) fixnum-tag)))
      (JO (@PCR ,(dict 'label)))
      (ROR Q (R ,(dict 'reg)) (&U ,scheme-type-width)))))

(define-lapopt 'GENERIC-ADD-CONST-ALIAS-TAG
  `((ADD Q (R (? temp)) (& (? const)))
    (JO (@PCR (? label)))
    (MOV Q (R (? target)) (R (? temp)))
    (OR Q (R (? target)) (&U ,fixnum-tag))
    (ROR Q (R (? target)) (&U ,scheme-type-width)))
  #F
  (lambda (dict)
    `((ADD Q (R ,(dict 'temp)) (& ,(+ (dict 'const) fixnum-tag)))
      (JO (@PCR ,(dict 'label)))
      (MOV Q (R ,(dict 'target)) (R ,(dict 'temp)))
      (ROR Q (R ,(dict 'target)) (&U ,scheme-type-width)))))

(define-lapopt 'GENERIC-SUB-CONST-ALIAS-TAG
  `((SUB Q (R (? temp)) (& (? const)))
    (JO (@PCR (? label)))
    (MOV Q (R (? target)) (R (? temp)))
    (OR Q (R (? target)) (&U ,fixnum-tag))
    (ROR Q (R (? target)) (&U ,scheme-type-width)))
  #F
  (lambda (dict)
    `((SUB Q (R ,(dict 'temp)) (& ,(- (dict 'const) fixnum-tag)))
      (JO (@PCR ,(dict 'label)))
      (MOV Q (R ,(dict 'target)) (R ,(dict 'temp)))
      (ROR Q (R ,(dict 'target)) (&U ,scheme-type-width)))))

;; Similar tag-injection combining rule for fix:or is a little more
;; general.

(define-lapopt 'OR-OR
  `((OR Q (R (? reg)) (& (? const-1)))
    (OR Q (R (? reg)) (& (? const-2))))
  #F
  (lambda (dict)
    `((OR Q (R ,(dict 'reg))
	  (& ,(bitwise-ior (dict 'const-1) (dict 'const-2)))))))

;; XXX Should never have allowed &U in the syntax here; the instruction
;; stream has signed operands.

(define-lapopt 'OR-OR-U
  `((OR Q (? reg) (& (? const-1)))
    (OR Q (? reg) (&U (? const-2))))
  #F
  (lambda (dict)
    `((OR Q ,(dict 'reg)
	  (& ,(bitwise-ior (dict 'const-1) (dict 'const-2)))))))

;; These rules match a whole fixnum detag-AND/OR-retag operation.  In
;; principle, these operations could be done in rulfix.scm, but the
;; instruction combiner wants all the intermediate steps.

(define-lapopt 'FIXNUM-OR-CONST-IN-PLACE
  `((COMMENT (PEEPHOLE OBJECT->FIXNUM))
    (SAL Q (? reg) (&U ,scheme-type-width))
    (OR Q (? reg) (& (? const)))
    (OR Q (? reg) (&U ,fixnum-tag))
    (ROR Q (? reg) (&U ,scheme-type-width)))
  (lambda (dict)
    ;; Works only if the sign extension is zero extension; otherwise we
    ;; would set all the type bits to 1.
    (<= 0 (dict 'const) (- (expt 2 31) 1)))
  (lambda (dict)
    `((OR Q ,(dict 'reg)
	  (& ,(shift-right (dict 'const) scheme-type-width))))))

(define-lapopt 'FIXNUM-AND-CONST-IN-PLACE
  `((COMMENT (PEEPHOLE OBJECT->FIXNUM))
    (SAL Q (? reg) (&U ,scheme-type-width))
    (AND Q (? reg) (& (? const)))
    (OR Q (? reg) (&U ,fixnum-tag))
    (ROR Q (? reg) (&U ,scheme-type-width)))
  (lambda (dict)
    ;; Works only if the sign extension is one extension; otherwise we
    ;; would clear all the type bits to 0.
    (<= (- (expt 2 31)) (dict 'const) -1))
  (lambda (dict)
    `((AND Q ,(dict 'reg)
	   (& ,(shift-right (dict 'const) scheme-type-width))))))

;; FIXNUM-NOT.  The first (partial) pattern uses the XOR operation to
;; put the tag bits in the low part of the result.  This pattern
;; occurs in the hash table hash functions, where the OBJECT->FIXNUM
;; has been shared by CSE.

(define-lapopt 'FIXNUM-NOT-TAG
  `((NOT Q (? reg))
    (AND Q (? reg) (& #x-40))
    (OR Q (? reg) (&U ,fixnum-tag))
    (ROR Q (? reg) (&U ,scheme-type-width)))
  #F
  (lambda (dict)
    ;; Sign extension to 64 bits works in our favour here: with a
    ;; negative constant we NOT all the bits we can't reach from an
    ;; immediate.
    (let ((magic-bits (+ (* -1 (expt 2 scheme-type-width)) fixnum-tag)))
      (assert (< magic-bits 0))
      `((XOR Q ,(dict 'reg) (& ,magic-bits))
	(ROR Q ,(dict 'reg) (&U ,scheme-type-width))))))

(define-lapopt 'FIXNUM-NOT-IN-PLACE
  `((COMMENT (PEEPHOLE OBJECT->FIXNUM))
    (SAL Q (? reg) (&U ,scheme-type-width))
    (NOT Q (? reg))
    (AND Q (? reg) (& #x-40))
    (OR Q (? reg) (&U ,fixnum-tag))
    (ROR Q (? reg) (&U ,scheme-type-width)))
  #F
  (lambda (dict)
    `((ROL Q ,(dict 'reg) (&U ,scheme-type-width))
      (XOR Q ,(dict 'reg) (& ,(* -1 (expt 2 scheme-type-width))))
      (ROR Q ,(dict 'reg) (&U ,scheme-type-width)))))

;; CLOSURES
;;
;; This rule recognizes code duplicated at the end of the CONS-CLOSURE
;; and CONS-MULTICLOSURE and the following CONS-POINTER. (This happens
;; because of the hack of storing the entry point as a tagged object
;; in the closure to allow GC to work correctly with relative jumps in
;; the closure code.  A better fix would be to alter the GC to make
;; absolute the addresses during closure transport.)
;;
;; The rule relies on the fact the REG-TEMP is a temporary for the
;; expansions of CONS-CLOSURE and CONS-MULTICLOSURE, so it is dead
;; afterwards, and is specific in matching because it is the only code
;; that stores an entry at a negative offset from the free pointer.

(define-lapopt 'CONS-CLOSURE-FIXUP
  `((MOV Q (? reg-temp)
	 (&U ,(make-non-pointer-literal (ucode-type COMPILED-ENTRY) 0)))
    (OR Q (? reg-temp) (? reg-addr))
    (MOV Q (@RO ,regnum:free-pointer -8) (? reg-temp))
    (MOV Q (? reg-tagged-addr)
	 (&U ,(make-non-pointer-literal (ucode-type COMPILED-ENTRY) 0)))
    (OR Q (? reg-tagged-addr) (? reg-addr)))
  #F
  (lambda (dict)
    `((MOV Q ,(dict 'reg-tagged-addr)
	   (&U ,(make-non-pointer-literal (ucode-type COMPILED-ENTRY) 0)))
      (OR Q ,(dict 'reg-tagged-addr) ,(dict 'reg-addr))
      (MOV Q (@RO ,regnum:free-pointer -8) ,(dict 'reg-tagged-addr)))))