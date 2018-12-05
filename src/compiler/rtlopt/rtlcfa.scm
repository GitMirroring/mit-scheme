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

;;;; RTL Control Flow Analysis
;;; package: (compiler rtl-optimizer rtl-control-flow-analysis)

;;; Control flow analysis analyzes the conditional branches in the
;;; program's control flow to prove which predicates are guaranteed
;;; true and false on entry to each bblock.  The results of control
;;; flow analysis are used by common subexpression elimination, to
;;; identify additional aliases, and by dead code elimination, to prune
;;; branches that can be statically determined.
;;;
;;; (This is not what Olin Shivers called control flow analysis in his
;;; PhD dissertation, which in LIAR is 0-CFA and is called application
;;; simulation (fgopt/simapp.scm), which in turn gave LIAR its name,
;;; LIAR Imitates APPLY Recursively.)

(declare (usual-integrations))

;(define cfa:trace-level 2)
(define-integrable cfa:trace-level 0)

(define-integrable (cfa-trace level obj)
  (if (>= cfa:trace-level level)
      (parameterize ((param:printer-radix #x10))
	(write-line obj))
      (begin obj unspecific)))

;;; (RTL-CONTROL-FLOW-ANALYSIS <rgraphs>)
;;;
;;;     For each bblock in each rgraph of <rgraphs>, set the
;;;     entry-truths and entry-falsehoods of the bblock to a set of
;;;     predicates that can statically be proven to be true or false,
;;;     respectively, in that bblock.

(define (rtl-control-flow-analysis rgraphs)
  (cfa-trace 1 '(control-flow-analysis))
  (for-each analyze-rgraph rgraphs))

;;; (ANALYZE-RGRAPH <rgraph>)
;;;
;;;     Compute for each bblock in <rgraph> the set of all true
;;;     predicates and false predicates that are guaranteed on every
;;;     path into the bblock.

(define (analyze-rgraph rgraph)
  (cfa-trace 2 `(cfa rgraph ,(hash-object rgraph)))
  (fluid-let ((*current-rgraph* rgraph))
    ;; Initialize data structures.
    (for-each (lambda (bblock)
		(set-bblock-queued?! bblock #f)
		(set-bblock-entry-truths! bblock '())
		(set-bblock-entry-falsehoods! bblock '())
		#;#;
		(set-bblock-predecessors! bblock '())
		(set-bblock-successors! bblock '()))
	      (rgraph-bblocks rgraph))
    ;; Compute the parts of the control flow graph that are not
    ;; reflected in our CFG abstraction.
    ;;
    ;; XXX Can we actually take advantage of these, or does everything
    ;; get passed on the stack with no opportunity for dataflow
    ;; analysis to propagate it?  Registerization was kiboshed back in
    ;; the '80s; can/should we revive it?
    #;
    (for-each (lambda (bblock)
		(let ((rtl
		       (rinst-rtl (rinst-last (bblock-instructions bblock)))))
		  (cond ((and (not (rtl:assign? rtl))
			      (lookup-flow-method (rtl:expression-type rtl)))
			 => (lambda (method)
			      (method rtl bblock))))))
	      (rgraph-bblocks rgraph))
    ;; Iteratively add truths and falsehoods as we can prove them.
    ;; Start with the initial edges so we get all of them out of the
    ;; way before we consider bblocks with more than one entry edge, in
    ;; an attempt to avoid recomputation.
    (with-new-node-marks
      (lambda ()
	(let ((queue (make-queue)))
	  (for-each (lambda (edge)
		      (enqueue-bblock! (edge-right-node edge) queue))
		    (rgraph-initial-edges rgraph))
	  (do () ((queue-empty? queue))
	    (let ((bblock (dequeue! queue)))
	      (cfa-trace 3 `(cfa bblock ,bblock))
	      (set-bblock-queued?! bblock #f)
	      (analyze-bblock bblock queue)
	      unspecific))
	  unspecific)))
    (for-each
     (lambda (bblock)
       (assert (list? (bblock-entry-truths bblock)))
       (assert (list? (bblock-entry-falsehoods bblock)))
       (cfa-trace 2 `(true ,bblock ,@(bblock-entry-truths bblock)))
       (cfa-trace 2 `(false ,bblock ,@(bblock-entry-falsehoods bblock))))
     (rgraph-bblocks rgraph))
    ;; Clean up a bit.
    (for-each (lambda (bblock)
		(cfg-node-remove! bblock bblock-tag:queued?))
	      (rgraph-bblocks rgraph))
    unspecific))

;;; (ENQUEUE-BBLOCK! <bblock> <queue>)
;;;
;;;     If bblock is not currently queued, queue it.

(define (enqueue-bblock! bblock queue)
  (if (and bblock (not (bblock-queued? bblock)))
      (begin
	(set-bblock-queued?! bblock #t)
	(enqueue! queue bblock))))

;;; (ANALYZE-BBLOCK <bblock> <queue>)
;;;
;;;     Recompute the set of truths and falsehoods proven on entry to
;;;     <bblock>.  If any change, or if this is the first time we have
;;;     seen <bblock>, queue all bblocks it flows to for re-evaluation.

(define (analyze-bblock bblock queue)
  (let ((truths (bblock-entry-truths bblock))
	(falsehoods (bblock-entry-falsehoods bblock))
	(truths* (recompute-truths bblock))
	(falsehoods* (recompute-falsehoods bblock)))
    (assert (rtp-set<=? truths truths*))
    (assert (rtp-set<=? falsehoods falsehoods*))
    (if (or (not (node-marked? bblock))
	    (not (and (rtp-set=? truths truths*)
		      (rtp-set=? falsehoods falsehoods*))))
	(begin
	  (cfa-trace 3 `(update ,bblock ,truths* ,falsehoods*))
	  (node-mark! bblock)
	  (set-bblock-entry-truths! bblock truths*)
	  (set-bblock-entry-falsehoods! bblock falsehoods*)
	  (for-each (lambda (successor)
		      (enqueue-bblock! successor queue))
		    (bblock-successors bblock))
	  (if (snode? bblock)
	      (enqueue-bblock! (snode-next bblock) queue)
	      (begin
		(enqueue-bblock! (pnode-consequent bblock) queue)
		(enqueue-bblock! (pnode-alternative bblock) queue)))))))

;;; (RECOMPUTE-TRUTHS <bblock>)
;;;
;;;     Compute the set of predicates known to be true on entry to
;;;     <bblock>, which is the intersection of all truths on exit from
;;;     <bblock>'s predecessors.

(define (recompute-truths bblock)
  (rtp-set/intersection
   (map edge-exit-truths (node-previous-edges bblock))))

;;; (RECOMPUTE-FALSEHOODS <bblock>)
;;;
;;;     Compute the set of predicates known to be false on entry to
;;;     <bblock>, which is the intersection of all falsehoods on exit
;;;     from <bblock>'s predecessors.

(define (recompute-falsehoods bblock)
  (rtp-set/intersection
   (map edge-exit-falsehoods (node-previous-edges bblock))))

;;; (EDGE-EXIT-TRUTHS <edge>)
;;;
;;;     Compute the set of predicates known to be true on exit from
;;;     <edge>, which is the set of truths of the bblock it originates
;;;     from, plus the predicate that bblock ends with if <edge> is the
;;;     consequent edge, or its negation if <edge> is the alternative
;;;     edge.

(define (edge-exit-truths edge)
  (let ((predecessor (edge-left-node edge)))
    (if (not predecessor)
	'()
	(let ((truths (bblock-entry-truths predecessor)))
	  (if (and (pnode? predecessor)
		   (eq? edge (pnode-consequent-edge predecessor)))
	      (let* ((rinst (rinst-last (bblock-instructions predecessor)))
		     (rtl (rinst-rtl rinst)))
		(rtp-set/adjoin (canonicalize-rtl-predicate rtl) truths))
	      truths)))))

;;; (EDGE-EXIT-FALSEHOODS <edge>)
;;;
;;;     Compute the set of predicates known to be false on exit from
;;;     <edge>, which is the set of falsehoods of the bblock it
;;;     originates from, plus the predicate that bblock ends with if
;;;     <edge> is the alternative edge.

(define (edge-exit-falsehoods edge)
  (let ((predecessor (edge-left-node edge)))
    (if (not predecessor)
	'()
	(let ((falsehoods (bblock-entry-falsehoods predecessor)))
	  (if (and (pnode? predecessor)
		   (eq? edge (pnode-alternative-edge predecessor)))
	      (let* ((rinst (rinst-last (bblock-instructions predecessor)))
		     (rtl (rinst-rtl rinst)))
		(rtp-set/adjoin (canonicalize-rtl-predicate rtl) falsehoods))
	      falsehoods)))))

(define (bblock-successors bblock)
  bblock
  '())

#|
(define (procedure-flow-by-label! predecessor label)
  (let ((procedure (label->object label)))
    (assert (rtl-procedure? procedure))
    (let ((successor (rtl-procedure/entry-node procedure)))
      (set-bblock-predecessors!
       successor
       (eq-set-adjoin predecessor (bblock-predecessors successor)))
      (set-bblock-successors!
       predecessor
       (eq-set-adjoin successor (bblock-successors predecessor)))
      unspecific)))

(define flow-methods
  '())

(define (lookup-flow-method type)
  (let ((entry (assq type flow-methods)))
    (if entry
	(cdr entry)
	#f)))

(define (define-flow-method type method)
  (let ((entry (assq type flow-methods)))
    (if entry
	(error "Redefining block flow method:" type method)))
  (set! flow-methods (cons (cons type method) flow-methods))
  type)

(define-flow-method 'INVOCATION:JUMP
  (lambda (rtl predecessor)
    (procedure-flow-by-label! predecessor (rtl:invocation:jump-procedure rtl))
    unspecific))

;;; XXX We've lost this information by the time we get to RTL.

#;
(define-flow-method 'INVOCATION:COMPUTED-JUMP
  (lambda (rtl predecessor)
    (for-each (lambda (target)
		(procedure-flow! predecessor target))
	      ...)
    unspecific))

(define-flow-method 'INVOCATION:LEXPR
  (lambda (rtl predecessor)
    (procedure-flow-by-label! predecessor (rtl:invocation:lexpr-procedure rtl))
    unspecific))

;;; XXX We've lost this information by the time we get to RTL.

#;
(define-flow-method 'INVOCATION:COMPUTED-LEXPR
  (lambda (rtl predecessor)
    (for-each (lambda (target)
		(procedure-flow! predecessor target))
	      ...)
    unspecific))
|#

(define (commute-predicate pred)
  pred
  (error "There are no PRED-2-ARGSes in the world..."))

(define (commute-fixnum-predicate pred)
  (define (commute pred)
    (case pred
      ((UNSIGNED-LESS-THAN-FIXNUM?) 'UNSIGNED-GREATER-THAN-FIXNUM?)
      ((UNSIGNED-GREATER-THAN-FIXNUM?) 'UNSIGNED-LESS-THAN-FIXNUM?)
      ((EQUAL-FIXNUM?) 'EQUAL-FIXNUM?)
      ((LESS-THAN-FIXNUM?) 'GREATER-THAN-FIXNUM?)
      ((GREATER-THAN-FIXNUM?) 'LESS-THAN-FIXNUM?)
      (else (error "Unknown fixnum predicate:" pred))))
  (let ((pred* (commute pred)))
    (assert (eq? pred (commute pred*)))
    pred*))

(define (commute-flonum-predicate pred)
  (define (commute pred)
    (case pred
      ((FLONUM-EQUAL?) 'FLONUM-EQUAL?)
      ((FLONUM-LESS?) 'FLONUM-GREATER?)
      ((FLONUM-GREATER?) 'FLONUM-LESS?)
      ((FLONUM-IS-EQUAL?) 'FLONUM-IS-EQUAL?)
      ((FLONUM-IS-UNORDERED?) 'FLONUM-IS-UNORDERED?)
      ((FLONUM-IS-LESS-OR-GREATER?) 'FLONUM-IS-LESS-OR-GREATER?)
      ((FLONUM-IS-GREATER?) 'FLONUM-IS-LESS?)
      ((FLONUM-IS-LESS?) 'FLONUM-IS-GREATER?)
      ((FLONUM-IS-GREATER-OR-EQUAL?) 'FLONUM-IS-LESS-OR-EQUAL?)
      ((FLONUM-IS-LESS-OR-EQUAL?) 'FLONUM-IS-GREATER-OR-EQUAL?)
      (else (error "Unknown flonum predicate:" pred))))
  (let ((pred* (commute pred)))
    (assert (eq? pred (commute pred*)))
    pred*))

;;; XXX Lots of ways we could extend predicate sets.

(define (rtp-set<=? a b)
  (lset<= equal? a b))

(define (rtp-set=? a b)
  (lset= equal? a b))

(define (rtp-set/intersection sets)
  (reduce (lambda (a b) (lset-intersection equal? a b)) '() sets))

(define (rtp-set/adjoin x set)
  (lset-adjoin equal? set x))

(define (rtp-set/member? x set)
  (and (member x set) #t))

;;; RTL predicate canonicalization.  Currently this just puts
;;; commutative predicates with the lower register number first so that
;;; membership can be tested with EQUAL?.

(define (canonicalize-rtl-predicate predicate)
  (let loop
      ((predicate
	(let ((method
	       (lookup-predicate-method (rtl:expression-type predicate))))
	  (if method
	      (method predicate)
	      predicate))))
    (if (rtl:register? predicate)
	(or (register-known-value (rtl:register-number predicate)) predicate)
	(rtl:map-subexpressions predicate loop))))

(define predicate-methods
  '())

(define (lookup-predicate-method type)
  (let ((entry (assq type predicate-methods)))
    (if entry
	(cdr entry)
	#f)))

(define (define-predicate-method type method)
  (let ((entry (assq type predicate-methods)))
    (if entry
	(error "Redefining predicate method:" type method)))
  (set! predicate-methods (cons (cons type method) predicate-methods))
  type)

(define-predicate-method 'EQ-TEST
  (lambda (predicate)
    (let ((exp1 (rtl:eq-test-expression-1 predicate))
	  (exp2 (rtl:eq-test-expression-2 predicate)))
      (if (and (rtl:register? exp1)
	       (rtl:register? exp2)
	       (> (rtl:register-number exp1)
		  (rtl:register-number exp2)))
	  (list 'EQ-TEST exp2 exp1)	;XXX
	  predicate))))

(define (binary-predicate-commutator get-pred get-1 get-2 commutator)
  (lambda (predicate)
    (let ((pred (get-pred predicate))
	  (exp1 (get-1 predicate))
	  (exp2 (get-2 predicate)))
      (cond ((and (rtl:register? exp1)
		  (rtl:register? exp2)
		  (> (rtl:register-number exp1)
		     (rtl:register-number exp2))
		  (commutator pred))
	     => (lambda (pred*)
		  (list (car predicate) pred* exp2 exp1))) ;XXX
	    (else predicate)))))

(define-predicate-method 'PRED-2-ARGS
  (binary-predicate-commutator rtl:pred-2-args-predicate
			       rtl:pred-2-args-operand-1
			       rtl:pred-2-args-operand-2
			       commute-predicate))

(define-predicate-method 'FIXNUM-PRED-2-ARGS
  (binary-predicate-commutator rtl:fixnum-pred-2-args-predicate
			       rtl:fixnum-pred-2-args-operand-1
			       rtl:fixnum-pred-2-args-operand-2
			       commute-fixnum-predicate))

(define-predicate-method 'FLONUM-PRED-2-ARGS
  (binary-predicate-commutator rtl:flonum-pred-2-args-predicate
			       rtl:flonum-pred-2-args-operand-1
			       rtl:flonum-pred-2-args-operand-2
			       commute-flonum-predicate))

;;; XXX Put these into the bblock structure.

;; XXX Can't use node-marked?/node-mark! for this because we need to
;; enable and disable it.  We could just always requeue but we might
;; waste a lot of time needlessly recomputing the truth and falsehood
;; sets.  We can reuse live-at-entry, live-at-exit, and
;; new-live-at-exit/register-map, none of which is used before register
;; lifetime analysis.

(define bblock-tag:queued?
  'cfa-queued?)
(define bblock-tag:entry-truths
  'cfa-entry-truths)
(define bblock-tag:entry-falsehoods
  'cfa-entry-falsehoods)

(define (bblock-queued? bblock)
  (cfg-node-get bblock bblock-tag:queued?))
(define (set-bblock-queued?! bblock queued?)
  (cfg-node-put! bblock bblock-tag:queued? queued?))

(define (bblock-entry-truths bblock)
  (cfg-node-get bblock bblock-tag:entry-truths))
(define (set-bblock-entry-truths! bblock entry-truths)
  (cfg-node-put! bblock bblock-tag:entry-truths entry-truths))

(define (bblock-entry-falsehoods bblock)
  (cfg-node-get bblock bblock-tag:entry-falsehoods))
(define (set-bblock-entry-falsehoods! bblock entry-falsehoods)
  (cfg-node-put! bblock bblock-tag:entry-falsehoods entry-falsehoods))