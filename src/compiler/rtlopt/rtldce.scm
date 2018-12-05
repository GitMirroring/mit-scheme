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

;;;; RTL dead code elimination
;;; package: (compiler rtl-optimizer dead-code-elimination)

;;; Dead code elimination happens in three parts:
;;;
;;; - identifying statements that are proved true or false on entry to each
;;;   bblock (called control flow analysis here, and implemented in,
;;;   rtlcfa.scm);
;;;
;;; - pruning branches that can be statically determined (dead branch
;;;   elimination here); and
;;;
;;; - pruning blocks that are unreachable after pruning branches (a kind of
;;;   garbage collection, called dead block elimination here).

(declare (usual-integrations))

;(define dce:trace-level 3)
(define-integrable dce:trace-level 0)

(define-integrable (dce-trace level obj)
  (if (>= dce:trace-level level)
      (parameterize ((param:printer-radix #x10))
	(pp obj))))

;;; (DEAD-BRANCH-ELIMINATION <rgraphs>)
;;;
;;;	Prune dead branches in <rgraphs>, replacing pnodes by snodes
;;;	that connect to the known successor.

(define (dead-branch-elimination rgraphs)
  (dce-trace 1 '(dead-branch-elimination))
  (let ((pruned? #f))
    (for-each (lambda (rgraph)
		(fluid-let ((*current-rgraph* rgraph))
		  (for-each (lambda (bblock)
			      (if (and (pnode? bblock)
				       (prune-branch-if-dead! bblock rgraph))
				  (set! pruned? #t)))
			    (rgraph-bblocks rgraph))
		  (if pruned?
		      (dce-trace 1 `(pruned rgraph ,(hash-object rgraph))))
		  unspecific))
	      rgraphs)
    pruned?))

;;; (DEAD-BLOCK-ELIMINATION <rgraphs> <root> <procedures> <continuations>)
;;;
;;;	Trace all blocks reachable from <root>, after dead branch
;;;	elimination.  Delete any entry edges in any rgraph in <rgraphs>
;;;	that point to unreachable nodes.  Return a list of all RTL
;;;	procedures and a list of all RTL continuations in <procedures>
;;;	and <continuations>, respectively, whose entry nodes are
;;;	reachable from <root>.  The remainder are dead code.
;;;
;;;	<Root> may be an RTL procedure or an RTL expression.

(define (dead-block-elimination rgraphs root procedures continuations)
  (dce-trace 1 '(dead-block-elimination))
  (with-new-node-marks
    (lambda ()
      (trace-reachable-bblocks!
       (cond ((rtl-expr? root) (rtl-expr/entry-node root))
	     ((rtl-procedure? root) (rtl-procedure/entry-node root))
	     (else (error "Invalid RTL root:" root))))
      (for-each prune-unreachable-bblocks! rgraphs)
      (values (prune-unreachable-procedures procedures)
	      (prune-unreachable-continuations continuations)))))

;;; (PRUNE-BRANCH-IF-DEAD! <bblock> <rgraph>)
;;;
;;;	If the final instruction of <bblock>, a pnode, has a known
;;;	outcome from dataflow analysis, replace <bblock> in <rgraph> by
;;;	an snode whose successor is the only successor of <bblock> that
;;;	would be reached.

(define (prune-branch-if-dead! bblock rgraph)
  (assert (pblock? bblock))
  ;; See whether we can statically decide which way the branch goes.
  (let* ((rtl (rinst-rtl (rinst-last (bblock-instructions bblock))))
	 (decision (evaluate-decision rtl bblock)))
    (case decision
      ((#f #t)
       (dce-trace 2 `(determine branch ,bblock ,rtl => ,decision))
       ;; We can decide.  Get the edges, and pick which one is live and
       ;; which one is dead.
       (let ((consequent-edge (pnode-consequent-edge bblock))
	     (alternative-edge (pnode-alternative-edge bblock)))
	 (receive (live-edge dead-edge)
		  (if decision
		      (values consequent-edge alternative-edge)
		      (values alternative-edge consequent-edge))
	   ;; Find the next node of the live edge.
	   ;;
	   ;; - If there are any instructions prior to the predicate in
	   ;;   this bblock, replace this bblock by an sblock whose
	   ;;   successor is the live successor and whose instructions
	   ;;   are all but the last instruction of this bblock.
	   ;;
	   ;; - If the predicate is the only one, just rewire all our
	   ;;   predecessors to the live successor.
	   (let ((next (edge-next-node live-edge)))
	     (let* ((rinst (bblock-instructions bblock))
		    (rinst* (rinst-next rinst)))
	       (set-bblock-instructions! bblock (cons 'dead rinst)) ;paranoia
	       (if rinst*
		   (begin
		     ;; Delete all but the last instruction.
		     (let loop ((rinst rinst) (rinst* rinst*))
		       (let ((rinst** (rinst-next rinst*)))
			 (if rinst**
			     (loop rinst* rinst**)
			     (set-rinst-next! rinst #f))))
		     ;; Create a replacement sblock.
		     (let ((bblock* (make-sblock rinst)))
		       (dce-trace 3 `(add ,bblock* replacing ,bblock))
		       (add-rgraph-bblock! rgraph bblock*)
		       ;; Set the predecessors to point at
		       ;; bblock* instead.
		       (node-replace-on-right! bblock bblock*)
		       ;; Disconnect bblock's edges to its live
		       ;; and dead successors.
		       (edge-disconnect-right! live-edge)
		       (edge-disconnect-right! dead-edge)
		       ;; Create an edge from bblock* to the live
		       ;; successor.
		       (create-edge! bblock* set-snode-next-edge! next)
		       bblock*))
		   (begin
		     (dce-trace 3 `(add nothing replacing ,bblock))
		     ;; Set the predecessors to point at next instead.
		     (node-replace-on-right! bblock next)
		     ;; Disconnect bblock's edges to its live and dead
		     ;; successors.
		     (edge-disconnect-right! live-edge)
		     (edge-disconnect-right! dead-edge)
		     next))))))
       ;; This bblock is no longer wired, so delete it from the rgraph.
       (dce-trace 3 `(delete ,bblock))
       (delete-rgraph-bblock! rgraph bblock)
       #t)
      ((BOTH)
       (dce-trace 3 `(both live ,bblock ,rtl ,(canonicalize-rtl-predicate rtl)))
       ;; Both edges are potentially still live.  Tough.
       #f)
      (else (error "Invalid pruning decision:" decision)))))

(define (evaluate-decision rtl bblock)
  (let ((rtl* (canonicalize-rtl-predicate rtl)))
    (cond ((rtp-set/member? rtl* (bblock-entry-truths bblock))
	   (dce-trace 2 `(cfa proved ,rtl true in ,bblock))
	   #t)
	  ((rtp-set/member? rtl* (bblock-entry-falsehoods bblock))
	   (dce-trace 2 `(cfa proved ,rtl false in ,bblock))
	   #f)
	  (else
	   ((lookup-pruning-method (rtl:expression-type rtl*)) rtl* bblock)))))

(define pruning-methods
  '())

(define (lookup-pruning-method type)
  (let ((entry (assq type pruning-methods)))
    (if (not entry)
	(error "Missing branch pruning method:" type))
    (cdr entry)))

(define (define-pruning-method type method)
  (let ((entry (assq type pruning-methods)))
    (if entry
	(error "Redefining branch pruning method:" type method)))
  (set! pruning-methods (cons (cons type method) pruning-methods))
  type)

(define (expression-known-value expression bblock)
  bblock				;XXX Use block-specific knowledge.
  (if (rtl:register? expression)
      (register-known-value (rtl:register-number expression))
      expression))

(define-pruning-method 'TYPE-TEST
  (lambda (stmt bblock)
    (let ((expression
	   (expression-known-value (rtl:type-test-expression stmt) bblock)))
      (if (rtl:machine-constant? expression)
	  (= (rtl:machine-constant-value expression)
	     (rtl:type-test-type stmt))
	  (begin
	    (dce-trace 2 `(fail ,stmt ,bblock))
	    'BOTH)))))

(define-pruning-method 'PRED-1-ARG
  (lambda (stmt bblock)
    stmt bblock
    'BOTH))

(define-pruning-method 'FIXNUM-PRED-1-ARG
  (lambda (stmt bblock)
    stmt bblock
    'BOTH))

(define-pruning-method 'FLONUM-PRED-1-ARG
  (lambda (stmt bblock)
    stmt bblock
    'BOTH))

(define-pruning-method 'EQ-TEST
  (lambda (stmt bblock)
    (let ((exp1 (rtl:eq-test-expression-1 stmt))
	  (exp2 (rtl:eq-test-expression-2 stmt)))
      ;; XXX Check recursively for things that are not register
      ;; references, and rule out the branch in those cases.
      (if (or (equal? exp1 exp2)
	      (let ((val1 (expression-known-value exp1 bblock))
		    (val2 (expression-known-value exp2 bblock)))
		(and val1 val2 (equal? val1 val2))))
	  #t
	  'BOTH))))

(define-pruning-method 'PRED-2-ARGS
  (lambda (stmt bblock)
    stmt bblock
    'BOTH))

(define-pruning-method 'FIXNUM-PRED-2-ARGS
  (lambda (stmt bblock)
    stmt bblock
    'BOTH))

(define-pruning-method 'FLONUM-PRED-2-ARGS
  (lambda (stmt bblock)
    stmt bblock
    'BOTH))

(define-pruning-method 'OVERFLOW-TEST
  (lambda (stmt bblock)
    stmt bblock
    'BOTH))

;;; (TRACE-REACHABLE-BLOCKS! <entry-bblock>)
;;;
;;;	Perform a breadth-first search to mark every bblock reachable
;;;	from <entry-bblock>.

(define (trace-reachable-bblocks! entry-bblock)
  (let ((queue (make-queue)))
    (bblock-reachable! entry-bblock queue)
    (do () ((queue-empty? queue))
      (let ((bblock (dequeue! queue)))
	(bblock-walk-forward bblock
	  (lambda (rinst)
	    (let loop ((rtl (rinst-rtl rinst)))
	      (cond ((rtl:assign? rtl)
		     (rtl:for-each-subexpression rtl loop))
		    ((rtl:register? rtl)
		     unspecific)
		    ((lookup-reachability-method (rtl:expression-type rtl))
		     => (lambda (method)
			  (method rtl queue)))
		    (else
		     (rtl:for-each-subexpression rtl loop))))))
	(if (snode? bblock)
	    (let ((next (snode-next bblock)))
	      (if next (bblock-reachable! next queue))
	      unspecific)
	    (let ((consequent (pnode-consequent bblock))
		  (alternative (pnode-alternative bblock)))
	      (if consequent (bblock-reachable! consequent queue))
	      (if alternative (bblock-reachable! alternative queue))
	      unspecific))
	unspecific))
    unspecific))

(define (bblock-reachable! bblock queue)
  (if (not (node-marked? bblock))
      (begin
	(node-mark! bblock)
	(enqueue! queue bblock))))

(define (procedure-reachable-by-label! label queue)
  (let ((procedure (label->object label)))
    (assert (rtl-procedure? procedure))
    (bblock-reachable! (rtl-procedure/entry-node procedure) queue)
    unspecific))

(define (continuation-reachable-by-label! label queue)
  (let ((continuation (label->object label)))
    (assert (rtl-continuation? continuation))
    (bblock-reachable! (rtl-continuation/entry-node continuation) queue)
    unspecific))

(define reachability-methods
  '())

(define (lookup-reachability-method type)
  (let ((entry (assq type reachability-methods)))
    (if entry
	(cdr entry)
	#f)))

(define (define-reachability-method type method)
  (let ((entry (assq type reachability-methods)))
    (if entry
	(error "Redefining block reachability method:" type method)))
  (set! reachability-methods (cons (cons type method) reachability-methods))
  type)

(define-reachability-method 'ENTRY:PROCEDURE
  (lambda (rtl queue)
    (let ((label (rtl:entry:procedure-procedure rtl)))
      (procedure-reachable-by-label! label queue))
    unspecific))

(define-reachability-method 'ENTRY:CONTINUATION
  (lambda (rtl queue)
    (let ((label (rtl:entry:continuation-continuation rtl)))
      (continuation-reachable-by-label! label queue))
    unspecific))

(define-reachability-method 'INVOCATION:APPLY
  (lambda (rtl queue)
    (let ((label (rtl:invocation:apply-continuation rtl)))
      (if label
	  (continuation-reachable-by-label! label queue)))
    unspecific))

(define-reachability-method 'INVOCATION:JUMP
  (lambda (rtl queue)
    (let ((label (rtl:invocation:jump-continuation rtl)))
      (if label
	  (continuation-reachable-by-label! label queue)))
    (procedure-reachable-by-label! (rtl:invocation:jump-procedure rtl) queue)
    unspecific))

(define-reachability-method 'INVOCATION:COMPUTED-JUMP
  (lambda (rtl queue)
    (let ((label (rtl:invocation:computed-jump-continuation rtl)))
      (if label
	  (continuation-reachable-by-label! label queue)))
    unspecific))

(define-reachability-method 'INVOCATION:LEXPR
  (lambda (rtl queue)
    (let ((label (rtl:invocation:lexpr-continuation rtl)))
      (if label
	  (continuation-reachable-by-label! label queue)))
    (procedure-reachable-by-label! (rtl:invocation:lexpr-procedure rtl)
				   queue)
    unspecific))

(define-reachability-method 'INVOCATION:COMPUTED-LEXPR
  (lambda (rtl queue)
    (let ((label (rtl:invocation:lexpr-continuation rtl)))
      (if label
	  (continuation-reachable-by-label! label queue)))
    unspecific))

(define-reachability-method 'INVOCATION:UUO-LINK
  (lambda (rtl queue)
    (let ((label (rtl:invocation:uuo-link-continuation rtl)))
      (if label
	  (continuation-reachable-by-label! label queue)))
    unspecific))

(define-reachability-method 'INVOCATION:GLOBAL-LINK
  (lambda (rtl queue)
    (let ((label (rtl:invocation:global-link-continuation rtl)))
      (if label
	  (continuation-reachable-by-label! label queue)))
    unspecific))

(define-reachability-method 'INVOCATION:PRIMITIVE
  (lambda (rtl queue)
    (let ((label (rtl:invocation:primitive-continuation rtl)))
      (if label
	  (continuation-reachable-by-label! label queue)))
    unspecific))

(define-reachability-method 'INVOCATION:SPECIAL-PRIMITIVE
  (lambda (rtl queue)
    (let ((label (rtl:invocation:special-primitive-continuation rtl)))
      (if label
	  (continuation-reachable-by-label! label queue)))
    unspecific))

(define-reachability-method 'INVOCATION:CACHE-REFERENCE
  (lambda (rtl queue)
    (let ((label (rtl:invocation:cache-reference-continuation rtl)))
      (if label
	  (continuation-reachable-by-label! label queue)))
    unspecific))

(define-reachability-method 'INVOCATION:LOOKUP
  (lambda (rtl queue)
    (let ((label (rtl:invocation:lookup-continuation rtl)))
      (if label
	  (continuation-reachable-by-label! label queue)))
    unspecific))

;;; (PRUNE-UNREACHABLE-BBLOCKS! <rgraph>)
;;;
;;;	For each bblock in <rgraph> that is not marked, meaning it is
;;;	not reachable from the entry, disconnect that bblock from the
;;;	CFG so that no reachable bblock has a previous edge originating
;;;	from it, and remove it from <rgraph>'s list of bblocks.  For
;;;	each entry edge in <rgraph> to a bblock that is unreachable,
;;;	remove that entry edge from <rgraph>'s list of entry edges.

(define (prune-unreachable-bblocks! rgraph)
  (let ((deletions '()))
    ;; Disconnect the unreachable bblocks and add them to the list of
    ;; deletions.
    (for-each (lambda (bblock)
		(define (disconnect! edge)
		  (if edge
		      (begin
			(dce-trace
			 3
			 `(disconnect ,bblock => ,(edge-right-node edge)))
			(edge-disconnect-right! edge))))
		(if (not (node-marked? bblock))
		    (begin
		      (dce-trace 2 `(prune block ,bblock))
		      (set! deletions (cons bblock deletions))
		      (if (snode? bblock)
			  (disconnect! (snode-next-edge bblock))
			  (begin
			    (disconnect! (pnode-consequent-edge bblock))
			    (disconnect! (pnode-alternative-edge bblock))))))
		unspecific)
	      (rgraph-bblocks rgraph))
    ;; Confirm that we deleted all the dead predecessors.
    (for-each (lambda (bblock)
		(if (node-marked? bblock)
		    (for-each (lambda (edge)
				(let ((predecessor (edge-left-node edge)))
				  (if predecessor
				      (assert (node-marked? predecessor)))
				  unspecific))
			      (node-previous-edges bblock)))
		unspecific)
	      (rgraph-bblocks rgraph))
    ;; Perform deletions on the list of bblocks.
    (set-rgraph-bblocks! rgraph
			 (eq-set-difference (rgraph-bblocks rgraph)
					    deletions)))
  ;; Delete the entry edges connected to unreachable bblocks.
  (set-rgraph-entry-edges!
   rgraph
   (filter (lambda (edge)
	     (if (not (node-marked? (edge-right-node edge)))
		 (dce-trace 3 `(prune entry ,(edge-right-node edge))))
	     (node-marked? (edge-right-node edge)))
	   (rgraph-entry-edges rgraph))))

;;; (PRUNE-UNREACHABLE-PROCEDURES <procedures>)
;;;
;;;	Return a list of the procedures in the list <procedures> whose
;;;	entry bblocks are reachable.

(define (prune-unreachable-procedures procedures)
  (filter (lambda (procedure)
	    (if (not (node-marked? (rtl-procedure/entry-node procedure)))
		(dce-trace 2 `(prune procedure ,procedure)))
	    (node-marked? (rtl-procedure/entry-node procedure)))
	  procedures))

;;; (PRUNE-UNREACHABLE-CONTINUATIONS <continuations>)
;;;
;;;	Return a list of the continuations in the list <continuations>
;;;	whose entry bblocks are reachable.

(define (prune-unreachable-continuations continuations)
  (filter (lambda (continuation)
	    (if (not (node-marked? (rtl-continuation/entry-node continuation)))
		(dce-trace 2 `(prune continuation ,continuation)))
	    (node-marked? (rtl-continuation/entry-node continuation)))
	  continuations))