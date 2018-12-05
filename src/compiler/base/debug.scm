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

;;;; Compiler Debugging Support

(declare (usual-integrations))

(define (po object)
  (let ((object (->tagged-vector object)))
    (write-line object)
    (for-each pp ((tagged-vector/description object) object))))

(define (debug/find-procedure name)
  (let loop ((procedures *procedures*))
    (and (pair? procedures)
	 (if (and (not (procedure-continuation? (car procedures)))
		  (or (eq? name (procedure-name (car procedures)))
		      (eq? name (procedure-label (car procedures)))))
	     (car procedures)
	     (loop (cdr procedures))))))

(define (debug/find-continuation number)
  (let ((label
	 (intern (string-append "continuation-" (number->string number)))))
    (let loop ((procedures *procedures*))
      (and (pair? procedures)
	   (if (and (procedure-continuation? (car procedures))
		    (eq? label (procedure-label (car procedures))))
	       (car procedures)
	       (loop (cdr procedures)))))))

(define (debug/find-entry-node node)
  (let ((node (->tagged-vector node)))
    (if (eq? (expression-entry-node *root-expression*) node)
	(write-line *root-expression*))
    (for-each (lambda (procedure)
		(if (eq? (procedure-entry-node procedure) node)
		    (write-line procedure)))
	      *procedures*)))

(define (debug/where object)
  (cond ((compiled-code-block? object)
	 (write-line (compiled-code-block/debugging-info object)))
	((compiled-code-address? object)
	 (write-line
	  (compiled-code-block/debugging-info
	   (compiled-code-address->block object)))
	 (write-string "Offset: ")
	 (write-string
	  (number->string (compiled-code-address->offset object) 16))
	 (newline))
	(else
	 (error "debug/where -- what?" object))))

(define (write-rtl-instructions rtl port)
  (write-instructions
   (lambda ()
     (parameterize ((current-output-port port))
       (for-each show-rtl-instruction rtl)))))

(define (dump-rtl filename)
  (write-instructions
   (lambda ()
     (with-output-to-file (pathname-new-type (->pathname filename) "rtl")
       (lambda ()
	 (for-each show-rtl-instruction (linearize-rtl *rtl-graphs*)))))))

(define (show-rtl rtl)
  (pp-instructions
   (lambda ()
     (for-each show-rtl-instruction rtl)))
  (newline))

(define (show-bblock-rtl bblock)
  (pp-instructions
   (lambda ()
     (bblock-walk-forward (->tagged-vector bblock)
       (lambda (rinst)
	 (show-rtl-instruction (rinst-rtl rinst))))))
  (newline))

(define (write-instructions thunk)
  (fluid-let ((*show-instruction* write))
    (parameterize ((param:printer-radix 16)
		   (param:print-uninterned-symbols-by-name? #t))
      (thunk))))

(define (pp-instructions thunk)
  (fluid-let ((*show-instruction* pretty-print))
    (parameterize ((param:pp-primitives-by-name? #f)
		   (param:printer-radix 16)
		   (param:print-uninterned-symbols-by-name? #t))
      (thunk))))

(define *show-instruction*)

(define (show-rtl-instruction rtl)
  (if (memq (car rtl)
	    '(LABEL CONTINUATION-ENTRY CONTINUATION-HEADER IC-PROCEDURE-HEADER
		    OPEN-PROCEDURE-HEADER PROCEDURE-HEADER CLOSURE-HEADER))
      (newline))
  (*show-instruction* rtl)
  (newline))

(define procedure-queue)
(define procedures-located)

(define (show-fg)
  (fluid-let ((procedure-queue (make-queue))
	      (procedures-located '()))
    (write-string "---------- Expression ----------")
    (newline)
    (fg/print-object *root-expression*)
    (with-new-node-marks
     (lambda ()
       (fg/print-entry-node (expression-entry-node *root-expression*))
       (queue-map!/unsafe procedure-queue
	 (lambda (procedure)
	   (newline)
	   (if (procedure-continuation? procedure)
	       (write-string "---------- Continuation ----------")
	       (write-string "---------- Procedure ----------"))
	   (newline)
	   (fg/print-object procedure)
	   (fg/print-entry-node (procedure-entry-node procedure))))))
    (newline)
    (write-string "---------- Blocks ----------")
    (newline)
    (fg/print-blocks (expression-block *root-expression*))))

(define (show-fg-node node)
  (fluid-let ((procedure-queue #f))
    (with-new-node-marks
     (lambda ()
       (fg/print-entry-node
	(let ((node (->tagged-vector node)))
	  (if (procedure? node)
	      (procedure-entry-node node)
	      node)))))))

(define (fg/print-entry-node node)
  (if node
      (fg/print-node node)))

(define (fg/print-object object)
  (po object)
  (newline))

(define (fg/print-blocks block)
  (fg/print-object block)
  (for-each fg/print-object (block-bound-variables block))
  (if (not (block-parent block))
      (for-each fg/print-object (block-free-variables block)))
  (for-each fg/print-blocks (block-children block))
  (for-each fg/print-blocks (block-disowned-children block)))

(define (fg/print-node node)
  (if (and node
	   (not (node-marked? node)))
      (begin
	(node-mark! node)
	(fg/print-object node)
	(cfg-node-case (tagged-vector/tag node)
	  ((PARALLEL)
	   (for-each fg/print-subproblem (parallel-subproblems node))
	   (fg/print-node (snode-next node)))
	  ((APPLICATION)
	   (fg/print-rvalue (application-operator node))
	   (for-each fg/print-rvalue (application-operands node)))
	  ((VIRTUAL-RETURN)
	   (fg/print-rvalue (virtual-return-operand node))
	   (fg/print-node (snode-next node)))
	  ((POP)
	   (fg/print-rvalue (pop-continuation node))
	   (fg/print-node (snode-next node)))
	  ((ASSIGNMENT)
	   (fg/print-rvalue (assignment-rvalue node))
	   (fg/print-node (snode-next node)))
	  ((DEFINITION)
	   (fg/print-rvalue (definition-rvalue node))
	   (fg/print-node (snode-next node)))
	  ((TRUE-TEST)
	   (fg/print-rvalue (true-test-rvalue node))
	   (fg/print-node (pnode-consequent node))
	   (fg/print-node (pnode-alternative node)))
	  ((STACK-OVERWRITE FG-NOOP)
	   (fg/print-node (snode-next node)))))))

(define (fg/print-rvalue rvalue)
  (if procedure-queue
      (let ((rvalue (rvalue-known-value rvalue)))
	(if (and rvalue
		 (rvalue/procedure? rvalue)
		 (not (memq rvalue procedures-located)))
	    (begin
	      (set! procedures-located (cons rvalue procedures-located))
	      (enqueue!/unsafe procedure-queue rvalue))))))

(define (fg/print-subproblem subproblem)
  (fg/print-object subproblem)
  (if (subproblem-canonical? subproblem)
      (fg/print-rvalue (subproblem-continuation subproblem)))
  (let ((prefix (subproblem-prefix subproblem)))
    (if (not (cfg-null? prefix))
	(fg/print-node (cfg-entry-node prefix)))))

;;;; FG in Scheme-like notation

(define (fg->sexp obj)
  (with-new-node-marks
    (lambda ()
      (cond ((rvalue? obj) (rvalue->sexp obj))
	    ((or (snode? obj) (pnode? obj)) (node->sexp obj))
	    (else (error "Unknown FG object type:" obj))))))

(define (node->sexp node)
  `(BEGIN ,@(node->sexp* node)))

(define (node->sexp* node)
  (if (node-marked? node)
      `('(,(hash-object node)))
      (begin
	(node-mark! node)
	`(',(hash-object node)
	  ,@(%node->sexp node)))))

(define (snode-next->sexp* node)
  (let ((next (snode-next node)))
    (if next
	(node->sexp* next)
	'())))

(define (%node->sexp node)
  (cfg-node-case (tagged-vector/tag node)
    ((APPLICATION) (application->sexp node))
    ((PARALLEL) (parallel->sexp node))
    ((ASSIGNMENT) (assignment->sexp node))
    ((DEFINITION) (definition->sexp node))
    ((TRUE-TEST) (true-test->sexp node))
    ((FG-NOOP) (fg-noop->sexp node))
    ((VIRTUAL-RETURN) (virtual-return->sexp node))
    ((POP) (pop->sexp node))
    ((STACK-OVERWRITE) (stack-overwrite->sexp node))
    (else (error "invalid"))))

(define (application->sexp app)
  (let* ((operator (rvalue->sexp (application-operator app)))
	 (operands (map rvalue->sexp (application-operands app)))
	 (next (snode-next->sexp* app)))
    (cond ((and (eq? 'COMBINATION (application-type app))
		(rvalue/procedure? (car (application-operands app))))
	   (let ((cont (car operands)))
	     (assert (eq? 'LAMBDA (car cont)))
	     (let ((bvl (cadr cont))
		   (body (cddr cont)))
	       (assert (= 1 (length bvl)))
	       (let ((var (car bvl)))
		 `((LET ((,var (,operator ,@(cdr operands))))
		     ,@body
		     ,@next))))))
	  ((and (eq? 'RETURN (application-type app))
		(rvalue/procedure? (application-operator app)))
	   (let ((cont operator))
	     (assert (eq? 'LAMBDA (car cont)))
	     (let ((vars (cadr cont))
		   (body (cddr cont)))
	       (assert (list? vars))
	       (assert (not (memq #!optional vars)))
	       `((LET ,(map list vars operands)
		   ,@body
		   ,@next)))))
	  (else
	   `((,operator ,@operands)
	     ,@next)))))

(define (parallel->sexp par)
  (let ((subproblems (parallel-subproblems par)))
    (define (subproblem-variable subproblem)
      (and (subproblem-canonical? subproblem)
	   (variable-id
	    (car (procedure-required (subproblem-continuation subproblem))))))
    (define (subproblem-expression subproblem)
      (and (subproblem-canonical? subproblem)
	   (node->sexp (subproblem-entry-node subproblem))))
    (assert (eq? (snode-next par) (parallel-application-node par)))
    (let* ((vars (filter-map subproblem-variable subproblems))
	   (exps (filter-map subproblem-expression subproblems))
	   (app (node->sexp* (parallel-application-node par))))
      `((PARALLEL ,@(map list vars exps))
	,@app))))

(define (assignment->sexp assignment)
  (let* ((lvalue (variable-id (assignment-lvalue assignment)))
	 (rvalue (rvalue->sexp (assignment-rvalue assignment)))
	 (next (snode-next->sexp* assignment)))
    `((SET! ,lvalue ,rvalue)
      ,@next)))

(define (definition->sexp def)
  (let* ((lvalue (variable-id (definition-lvalue def)))
	 (rvalue (rvalue->sexp (definition-rvalue def)))
	 (next (snode-next->sexp* def)))
    `((DEFINE ,lvalue ,rvalue)
      ,@next)))

(define (true-test->sexp test)
  (let* ((rvalue (rvalue->sexp (true-test-rvalue test)))
	 (con (node->sexp (pnode-consequent test)))
	 (alt (node->sexp (pnode-alternative test))))
    ;; XXX Find the join point and follow with it?
    `((IF ,rvalue ,con ,alt))))

(define (fg-noop->sexp node)
  `((NOOP)
    ,@(snode-next->sexp* node)))

(define (virtual-return->sexp vret)
  (let* ((type
	  (enumeration/index->name continuation-types
				   (virtual-continuation/type
				    (virtual-return-operator vret))))
	 (operand
	  (let ((operand (virtual-return-operand vret)))
	    (if (rvalue/continuation? operand)
		(continuation-id operand)
		(rvalue->sexp operand))))
	 (next (snode-next->sexp* vret)))
    `((VIRTUAL ,type ,operand)
      ,@next)))

(define (pop->sexp pop)
  (let* ((cont (continuation-id (pop-continuation pop)))
	 (next (snode-next->sexp* pop)))
    `((POP ,cont)
      ,@next)))

(define (stack-overwrite->sexp so)
  (let* ((target (variable-id (stack-overwrite-target so)))
	 (cont (continuation-id (stack-overwrite-continuation so)))
	 (next (snode-next->sexp* so)))
    `((STACK-OVERWRITE ,target ,cont)
      ,@next)))

(define (rvalue->sexp rvalue)
  (cond ((reference? rvalue) (reference->sexp rvalue))
	((procedure? rvalue) (procedure->sexp rvalue))
	((constant? rvalue) (constant->sexp rvalue))
	((block? rvalue) (block->sexp rvalue))
	((unassigned-test? rvalue) (unassigned-test->sexp rvalue))
	((expression? rvalue) (expression->sexp rvalue))
	(else rvalue)))

(define (reference->sexp rvalue)
  (variable-id (reference-lvalue rvalue)))

(define (procedure->sexp proc)
  (let* ((bvl
	  (procedure-bvl->sexp (procedure-required proc)
			       (procedure-optional proc)
			       (procedure-rest proc)))
	 (defs
	  (procedure-defs->sexp (procedure-names proc)
				(procedure-values proc)))
	 (body
	  (node->sexp* (procedure-entry-node proc))))
    `(LAMBDA ,bvl
       '(,(procedure-id proc)
	 ,(enumeration/index->name continuation-types (procedure-type proc)))
       ,@defs
       ,@body)))

(define (procedure-bvl->sexp req opt rest)
  (let* ((req (map variable-id req))
	 (opt (map variable-id opt))
	 (rest (and rest (variable-id rest))))
    `(,@req ,@(if (pair? opt) `(#!OPTIONAL ,@opt) '()) . ,(or rest '()))))

(define (procedure-defs->sexp names values)
  (map (lambda (name value)
	 (let* ((var (variable-id name))
		(val (rvalue->sexp value)))
	   `(DEFINE ,var ,val)))
       names values))

(define (constant->sexp const)
  `',(constant-value const))

(define (block->sexp block)
  '(block))				;XXX ?

(define (unassigned-test->sexp ut)
  `(UNASSIGNED? ,(variable-id (unassigned-test-lvalue ut))))

(define (expression->sexp exp)
  (let* ((cont (variable-id (expression-continuation exp)))
	 (body (node->sexp* (expression-entry-node exp))))
    `(LAMBDA (,cont) 'EXPRESSION ,@body)))

(define (variable-id var)
  (symbol (case (variable-name var)
	    ((|#[continuation]|) 'c)	;abbreviate
	    ((|#[value]|) 'v)
	    (else (variable-name var)))
	  "." (hash-object var)))

(define (procedure-id proc)
  (if (procedure-continuation? proc)
      (let ((label (symbol->string (procedure-label proc)))
	    (prefix "continuation-"))
	;; Abbreviate a little bit for legibility.
	(assert (string-prefix? prefix label))
	(symbol 'C- (substring label (string-length prefix))))
      (procedure-label proc)))

(define (continuation-id cont)
  (if (procedure? cont)
      (procedure-id cont)
      (begin
	(assert (virtual-continuation? cont))
	(symbol 'VC. (hash-object cont)))))

;;;; RTL CFG with block numbers and without linearization

(define (dump-rtl-full root procedures continuations rgraphs port)
  (define (show-expr expr)
    (write-line expr port)
    (pp (rtl-expr/entry-node expr) port)
    (show-bblock (rtl-expr/entry-node expr) (rtl-expr/label expr))
    unspecific)
  (define (show-proc proc)
    (write-line proc port)
    (pp (rtl-procedure/entry-node proc) port)
    (show-bblock (rtl-procedure/entry-node proc) (rtl-procedure/label proc))
    unspecific)
  (define (show-cont cont)
    (write-line cont port)
    (pp (rtl-continuation/entry-node cont) port)
    (show-bblock (rtl-continuation/entry-node cont)
		 (rtl-continuation/label cont))
    unspecific)
  (define (show-rgraph rgraph)
    (let ((bblocks (rgraph-bblocks rgraph)))
      (if bblocks
          (begin
            (for-each (lambda (bblock)
                        (show-bblock bblock #f)
                        unspecific)
                      bblocks)
            unspecific))))
  (define (show-bblock bblock label)
    (if (not (node-marked? bblock))
	(begin
	  (node-mark! bblock)
	  (newline port)
	  (pp bblock port)
	  (if label
	      (pp (rtl:make-label-statement label) port))
	  (for-each (lambda (edge)
		      (let ((predecessor (edge-left-node edge)))
			(if predecessor
			    (pp `(from ,predecessor) port))))
		    (node-previous-edges bblock))
	  (bblock-walk-forward bblock
	    (lambda (rinst)
	      (pp (rinst-rtl rinst) port)))
	  (if (snode? bblock)
	      (let ((next (snode-next bblock)))
		(if next
		    (begin
		      (pp `(goto ,(snode-next bblock)) port)
		      (show-bblock (snode-next bblock) #f))
		    (pp '(not-reached) port)))
	      (begin
		(pp `(jump-if-true ,(pnode-consequent bblock)) port)
		(pp `(jump-if-false ,(pnode-alternative bblock)) port)
		(show-bblock (pnode-consequent bblock) #f)
		(show-bblock (pnode-alternative bblock) #f))))))
  (parameterize ((param:printer-radix #x10)
		 (param:print-uninterned-symbols-by-name? #t)
		 (param:pp-primitives-by-name? #f))
    (with-new-node-marks
      (lambda ()
	(pp `(root ,root) port)
	(cond ((rtl-expr? root) (show-expr root))
	      ((rtl-procedure? root) (show-proc root))
	      (else (error "Invalid root:" root)))
	(for-each (lambda (proc)
		    (if (not (eq? proc root))
			(begin
			  (newline port)
			  (show-proc proc)
                          unspecific)))
                  procedures)
	(for-each (lambda (cont)
		    (newline port)
		    (show-cont cont)
                    unspecific)
                  continuations)
	(newline port)
	(pp `(unreachable bblocks) port)
	(for-each show-rgraph rgraphs)))))
