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

;;;; Live variable analysis
;;; package: (compiler fg-optimizer live-variable-analysis)

(declare (usual-integrations))

(define (live-variable-analysis expression lvalues)
  (if compiler:analyze-live-variables?
      (begin
	(for-each initialize-lvalue-dependencies! lvalues)
	(with-new-node-marks
	  (lambda ()
	    (transitive-closure
	     (lambda () unspecific)
	     (lambda (node)
	       (cond ((expression? node) (analyze-expression node))
		     ((procedure? node) (analyze-procedure node))
		     ((lvalue? node) (analyze-lvalue node))
		     (else (error "Bad node:" node))))
	     (list expression))))
	(bkpt "Live variable analysis!")
	unspecific)))

(define (initialize-lvalue-dependencies! lvalue)
  ;; Assume that global variables are always useful, for assignments.
  (if (and (variable? lvalue)
	   (ic-block? (variable-block lvalue)))
      (set-lvalue-dependencies! lvalue #f)
      (set-lvalue-dependencies! lvalue '())))

(define (analyze-expression expression)
  (walk-node (expression-entry-node expression)))

(define (analyze-procedure procedure)
  (for-each lvalue-depends!
	    (procedure-names procedure)
	    (procedure-values procedure))
  (walk-node (procedure-entry-node procedure)))

(define (analyze-lvalue lvalue)
  (assert (variable? lvalue))
  (for-each (lambda (rvalue)
	      (rvalue-useful! rvalue `(needed by ,(variable-name lvalue))))
	    (let ((dependencies (lvalue-dependencies lvalue)))
	      (set-lvalue-dependencies! lvalue #f)
	      dependencies)))

(define (lvalue-useful? lvalue)
  (not (lvalue-dependencies lvalue)))

(define (lvalue-useless? lvalue)
  (not (lvalue-useful? lvalue)))

(define (lvalue-useful! lvalue why)
  (if (not (lvalue-useful? lvalue))
      (begin
	(assert (variable? lvalue))
	(pp `(useful ,(variable-name lvalue) ,why))
	(enqueue-node! lvalue))))

(define (lvalue-depends! lvalue rvalue)
  (if (lvalue-useful? lvalue)
      (rvalue-useful! rvalue)
      (let* ((dependencies (lvalue-dependencies lvalue))
	     (dependencies* (eq-set-adjoin rvalue dependencies)))
	(assert (variable? lvalue))
	(pp `(,(variable-name lvalue) depends on ,(write-to-string rvalue)))
	(set-lvalue-dependencies! lvalue dependencies*))))

(define (rvalue-useful! rvalue why)
  (cond ((rvalue/reference? rvalue) (reference-useful! rvalue why))
	((rvalue/procedure? rvalue) (procedure-useful! rvalue why))))

(define (reference-useful! reference why)
  (lvalue-useful! (reference-lvalue reference) why))

(define (procedure-useful! procedure why)
  (pp `(useful ,(procedure-name procedure) ,why))
  (enqueue-node! procedure))

(define (walk-next node)
  (if (and node (not (node-marked? node)))
      (begin (node-mark! node)
	     (walk-node node))))

(define (walk-node node)
  (cfg-node-case (tagged-vector/tag node)
    ((APPLICATION)
     (analyze-application node)
     (walk-next (snode-next node)))
    ((PARALLEL)
     (for-each (lambda (subproblem)
		 (let ((cfg (subproblem-prefix subproblem)))
		   (if (not (cfg-null? cfg))
		       (walk-next (cfg-entry-node cfg)))))
	       (parallel-subproblems node))
     (walk-next (snode-next node)))
    ((ASSIGNMENT)
     (lvalue-depends! (assignment-lvalue node) (assignment-rvalue node))
     (walk-next (snode-next node)))
    ((DEFINITION)
     (lvalue-depends! (definition-lvalue node) (definition-rvalue node))
     (walk-next (snode-next node)))
    ((TRUE-TEST)
     (rvalue-useful! (true-test-rvalue node) '(truth test))
     (walk-next (pnode-consequent node))
     (walk-next (pnode-alternative node)))
    ((VIRTUAL-RETURN)
     (rvalue-useful! (virtual-return-operand node) '(virtual-return))
     (walk-next (snode-next node)))
    ((FG-NOOP)
     (walk-next (snode-next node)))))

(define (analyze-application application)
  (let ((operator (application-operator application)))
    ;; XXX Why do we do this?  Won't analyze-combination and
    ;; analyze-return handle it if appropriate?
    (if (rvalue/procedure? operator)
	(procedure-useful! operator '(appears as immediate operator))))
  (cond ((application/combination? application)
	 (analyze-combination application))
	((application/return? application)
	 (analyze-return application))
	(else
	 (error "Invalid application:" application))))

(define (analyze-combination combination)
  (let ((operator (combination/operator combination))
	(continuation (combination/continuation combination))
	(operands (combination/operands combination)))
    (define (all-known-operators)
      ;; If every operator is a known procedure, then we can defer the
      ;; decision of what operands are live to those procedures, and
      ;; even disregard the continuation, because those procedures may
      ;; not use their continuations.
      (for-each (let ((operands (application-operands combination)))
		  (lambda (operator)
		    (simulate-application operator operands)))
		(rvalue-values operator))
      (rvalue-useful! operator '(appears as known operator)))
    (define (at-least-one-unknown-operator)
      ;; Assume that if the operator can be anything but a known
      ;; procedure, then it will return to its continuation.
      (rvalue-useful! continuation
		      '(appears as continuation of unknown operator))
      ;; In this case, the continuation's parameter depends on the
      ;; operator and operands of the combination.
      (for-each (lambda (continuation)
		  (assert (rvalue/continuation? continuation))
		  (for-each (let ((parameter
				   (continuation/parameter continuation)))
			      (lambda (rvalue)
				(lvalue-depends! parameter rvalue)))
			    (cons operator operands)))
		(rvalue-values continuation))
      ;; Since at least one of the operators is not known to us, we
      ;; can now say with certainty that the entire application is
      ;; useful if it has effects or its value will be passed out.
      (if (or (not (rvalue/side-effect-free? operator))
	      (rvalue-passed-in? continuation))
	  (let ((why
		 (if (not (rvalue/side-effect-free? operator))
		     '(may have side effects)
		     '(continuation passed in))))
	    (rvalue-useful! operator why)
	    (for-each (lambda (operand)
			(rvalue-useful! operand '(operand ,why)))
		      operands))))
    (cond ((rvalue-passed-in? operator)
	   (if (rvalue/side-effect-free? operator)
	       (at-least-one-unknown-operator)
	       (application-useful! combination '(passed in side effects))))
	  ((every rvalue/procedure? (rvalue-values operator))
	   (all-known-operators))
	  (else
	   (at-least-one-unknown-operator)))))

;;; True if rvalue is a procedure with no side effects.

(define (rvalue/side-effect-free? rvalue)
  (if (rvalue-passed-in? rvalue)
      (and (reference? rvalue)
	   (let ((lvalue (reference-lvalue rvalue)))
	     (and (variable? lvalue)
		  (variable/side-effect-free? lvalue))))
      (every (lambda (procedure)
	       (cond ((rvalue/constant? procedure)
		      (constant/side-effect-free? procedure))
		     ((rvalue/procedure? procedure)
		      (null? (procedure-side-effects procedure)))
		     (else #f)))
	     (rvalue-values rvalue))))

(define (application-useful! application why)
  (rvalue-useful! (application-operator application)
		  `(operator of useful application ,why))
  (for-each (lambda (operand)
	      (rvalue-useful! operand `(operand of useful application ,why)))
	    (application-operands application)))

(define (analyze-return return)
  (let ((operator (return/operator return)))
    (if (rvalue-passed-in? operator)
	(application-useful! return '(continuation passed in))
	(begin
	  (rvalue-useful! operator '(continuation i guess))
	  (for-each (let ((operand (return/operand return)))
		      (lambda (operator)
			(assert (rvalue/continuation? operator))
			(simulate-application operator (list operand))))
		    (rvalue-values operator))))))

(define (simulate-application procedure rvalues)
  (let loop ((required (procedure-required procedure)) (rvalues rvalues))
    (if (pair? required)
	(if (pair? rvalues)
	    (begin (lvalue-depends! (car required) (car rvalues))
		   (loop (cdr required) (cdr rvalues)))
	    ;; Silently ignore arity errors, which are warned of elsewhere.
	    unspecific)
	(let loop
	    ((optional (procedure-optional procedure)) (rvalues rvalues))
	  (if (pair? optional)
	      (if (pair? rvalues)
		  (begin (lvalue-depends! (car optional) (car rvalues))
			 (loop (cdr optional) (cdr rvalues)))
		  unspecific)
	      (if (pair? rvalues)
		  (let ((rest (procedure-rest procedure)))
		    (if rest
			(for-each (lambda (rvalue)
				    (lvalue-depends! rest rvalue))
				  rvalues)))))))))
