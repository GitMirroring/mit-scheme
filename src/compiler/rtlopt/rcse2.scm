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

;;;; RTL Common Subexpression Elimination
;;;  Based on the GNU C Compiler

(declare (usual-integrations))

;;;; Canonicalization

(define (expression-replace! statement-expression set-statement-expression!
			     statement receiver)
  ;; Replace the expression by its cheapest equivalent.  Returns two
  ;; values: (1) a flag which is true iff the expression is volatile;
  ;; and (2) a thunk which, when called, will insert the expression in
  ;; the hash table, returning the element.  Do not call the thunk if
  ;; the expression is volatile.
  (let ((expression
	 (expression-canonicalize
	  (expression-reduce (statement-expression statement)))))
    (full-expression-hash expression
      (lambda (hash volatile? in-memory?)
	(let ((element
	       (find-cheapest-valid-element expression hash volatile?)))
	  (let ((finish
		 (lambda (expression hash volatile? in-memory?)
		   (set-statement-expression! statement expression)
		   (receiver volatile?
			     (expression-inserter expression
						  element
						  hash
						  in-memory?)))))
	    (if element
		(let ((expression (element-expression element)))
		  (full-expression-hash expression
		    (lambda (hash volatile? in-memory?)
		      (finish expression hash volatile? in-memory?))))
		(finish expression hash volatile? in-memory?))))))))

(define ((expression-inserter expression element hash in-memory?))
  (or element
      (begin
	(if (rtl:register? expression)
	    (set-register-expression! (rtl:register-number expression)
				      expression)
	    (mention-registers! expression))
	(let ((element* (rcse-ht-insert! hash expression false)))
	  (set-element-in-memory?! element* in-memory?)
	  (element-first-value element*)))))

(define (expression-canonicalize expression)
  (cond ((rtl:register? expression)
	 (or (register-expression
	      (quantity-first-register
	       (get-register-quantity (rtl:register-number expression))))
	     expression))
	((stack-reference? expression)
	 (let ((register
		(quantity-first-register
		 (stack-reference-quantity expression))))
	   (or (and register (register-expression register))
	       expression)))
	(else
	 (rtl:map-subexpressions expression expression-canonicalize))))

;;;; Invertible expression elimination

;;; (EXPRESSION-REDUCE <expression>)
;;;
;;;	For each subexpression of <expression>, and for each equivalent
;;;	of that subexpression according to CSE, try substituting that
;;;	equivalent for that subexpression and reducing the whole
;;;	expression.  If it can be reduced, return the lowest-cost
;;;	expression that <expression> can be reduced to; otherwise just
;;;	return <expression>.
;;;
;;;	There should be no need to iterate this process, because every
;;;	expression is reduced like this as we go along, so each element
;;;	should always have a minimal expression to which no further
;;;	reductions apply.
;;;
;;;	XXX At merge blocks, consider applying this to every possible
;;;	expansion in _each_ predecessor, and taking the intersection of
;;;	the possible reductions.  That way, in (flo:+ x (if y (flo:* a
;;;	b) (flo:/ a b))), we could eliminate the type check, because
;;;	(object->type (float->object 123)) = (object->type
;;;	(float->object 456)) = (machine-constant (ucode-type flonum)).
;;;	For now, we'll just live with having to distribute it as (if y
;;;	(flo:+ x (flo:* a b)) (flo:+ x (flo:/ a b))) if we want to
;;;	avoid the type check.  This would not, unfortunately, eliminate
;;;	the intermediate float->object, because (object->float
;;;	(float->object 123)) is not, in general, equal to
;;;	(object->float (float->object 456)).  Addressing that would
;;;	require merging a common suffix of the predecessors in the
;;;	merge block, which would also address the type check.

(define (expression-reduce expression)
  (let ((matchers (reduction-matchers expression)))
    (if (not matchers)
	expression
	(let loop
	    ((substituticators (rtl:subexpression-substituticators expression))
	     (candidates '()))
	  (if (pair? substituticators)
	      ((car substituticators)
	       (lambda (subexpression substitute)
		 (define (consider subexpression* candidates)
		   (let* ((expression* (substitute subexpression*))
			  (expression**
			   (expression-reduce-1 expression* matchers)))
		     ;; If, after substitution, nothing changed, or we
		     ;; already had whatever reduction gave us, don't
		     ;; consider this as a new candidate.
		     (if (or (eq? expression** expression*)
			     (equal? expression** expression*)
			     (assoc expression** candidates))
			 candidates
			 (cons (list expression**
				     (rtl:expression-cost expression**))
			       candidates))))
		 (let* ((hash (expression-hash subexpression))
			(class (rcse-ht-lookup hash subexpression)))
		   (let subloop
		       ((element (and class (element-first-value class)))
			(candidates candidates))
		     (if (element? element)
			 (subloop (element-next-value element)
				  (consider (element-expression element)
					    candidates))
			 (loop (cdr substituticators) candidates))))))
	      (if (pair? candidates)
		  (caar (sort candidates (lambda (a b) (< (cadr a) (cadr b)))))
		  expression))))))

;;; (RTL:SUBEXPRESSION-SUBSTITUTICATORS <expression>)
;;;
;;;	Return a list of substituticators for the subexpressions of
;;;	<expression>.  A substituticator is a function that works like
;;;
;;;		(<substituticator>
;;;		 (LAMBDA (SUBEXPRESSION SUBSTITUTE)
;;;		   ... (SUBSTITUTE SUBEXPRESSION*) ...))
;;;
;;;	where SUBEXPRESSION one of the subexpressions of <expression>,
;;;	and (SUBSTITUTE* <subexpression*>) returns an expression that
;;;	is like <expression> but with <subexpression*> substituted for
;;;	that subexpression.
;;;
;;;	XXX Move this to rtlbase.

(define (rtl:subexpression-substituticators expression)
  (if (or (rtl:register? expression)
	  (rtl:contains-no-substitutable-registers? expression))
      '()
      (let ((type (car expression))
	    (subexpressions (cdr expression)))
	(let loop
	    ((subexpressions subexpressions)
	     (reverse-prefix (list type)))
	  (if (pair? subexpressions)
	      (let ((subexpression (car subexpressions))
		    (subexpressions (cdr subexpressions)))
		(let ((substituticators
		       (loop subexpressions
			     (cons subexpression reverse-prefix))))
		  (if (pair? subexpression)
		      (cons (lambda (f)
			      (f subexpression
				 (lambda (subexpression*)
				   (append-reverse reverse-prefix
						   (cons subexpression*
							 subexpressions)))))
			    substituticators)
		      substituticators)))
	      '())))))

(define (expression-reduce-1 expression matchers)
  (let ((reducer (pattern-lookup matchers expression)))
    (if reducer
	(reducer)
	expression)))

(define reduction-rules
  (make-strong-eq-hash-table))

(define (add-reduction-rule! pattern matcher)
  (assert (pair? pattern))
  (let ((keyword (car pattern)))
    (assert (symbol? keyword))
    (hash-table-update!/default reduction-rules keyword
      (lambda (rules) (cons matcher rules))
      '())
    unspecific))

(define (reduction-matchers expression)
  (and (pair? expression)
       (hash-table-ref/default reduction-rules (car expression) #f)))

(define-rule reduction (OBJECT->FIXNUM (FIXNUM->OBJECT (? x)))
  (QUALIFIER (expression-valid? x))
  x)

(define-rule reduction (FIXNUM->OBJECT (OBJECT->FIXNUM (? x)))
  (QUALIFIER (expression-valid? x))
  x)

(define-rule reduction (OBJECT->UNSIGNED-FIXNUM (FIXNUM->OBJECT (? x)))
  (QUALIFIER (expression-valid? x))
  x)

(define-rule reduction (FIXNUM->OBJECT (OBJECT->UNSIGNED-FIXNUM (? x)))
  (QUALIFIER (expression-valid? x))
  x)

(define-rule reduction (FIXNUM->ADDRESS (ADDRESS->FIXNUM (? x)))
  (QUALIFIER (expression-valid? x))
  x)

(define-rule reduction (ADDRESS->FIXNUM (FIXNUM->ADDRESS (? x)))
  (QUALIFIER (expression-valid? x))
  x)

(define-rule reduction (OBJECT->FLOAT (FLOAT->OBJECT (? x)))
  (QUALIFIER (expression-valid? x))
  x)

(define-rule reduction (FLOAT->OBJECT (OBJECT->FLOAT (? x)))
  (QUALIFIER (expression-valid? x))
  x)

(define-rule reduction
  (OBJECT->ADDRESS (CONS-POINTER (? type) (? address)))
  (QUALIFIER (expression-valid? address))
  type
  address)

(define-rule reduction
  (OBJECT->TYPE (CONS-POINTER (? type) (? address)))
  (QUALIFIER (expression-valid? type))
  address
  type)

(define-rule reduction
  (OBJECT->DATUM (CONS-NON-POINTER (? type)) (? datum))
  (QUALIFIER (expression-valid? datum))
  type
  datum)

(define-rule reduction
  (OBJECT->TYPE (CONS-NON-POINTER (? type)) (? datum))
  (QUALIFIER (expression-valid? type))
  datum
  type)

(define-rule reduction
  (OBJECT->TYPE (FLOAT->OBJECT (? float)))
  ;; Note: We don't require that float be a valid expression here: even
  ;; if it has been invalidated, no matter what the value would have
  ;; been, the type is always the same.
  float
  (rtl:make-machine-constant (ucode-type flonum)))

;;;; Hash

(define (expression-hash expression)
  (full-expression-hash expression
    (lambda (hash do-not-record? hash-arg-in-memory?)
      do-not-record? hash-arg-in-memory?
      hash)))

(define (full-expression-hash expression receiver)
  (let ((do-not-record? false)
	(hash-arg-in-memory? false))
    (define (loop expression)
      (let ((type (rtl:expression-type expression)))
	(+ (symbol-hash type)
	   (case type
	     ((REGISTER)
	      (quantity-number
	       (get-register-quantity (rtl:register-number expression))))
	     ((OFFSET)
	      ;; Note that stack-references do not get treated as
	      ;; memory for purposes of invalidation.  This is because
	      ;; (supposedly) no one ever accesses the stack directly
	      ;; except the compiler's output, which is explicit.
	      (if (interpreter-stack-pointer? (rtl:offset-base expression))
		  (quantity-number (stack-reference-quantity expression))
		  (begin
		    (set! hash-arg-in-memory? true)
		    (continue expression))))
	     ((BYTE-OFFSET)
	      (set! hash-arg-in-memory? true)
	      (continue expression))
	     ((PRE-INCREMENT POST-INCREMENT)
	      (set! hash-arg-in-memory? true)
	      (set! do-not-record? true)
	      0)
	     (else
	      (continue expression))))))

    (define (continue expression)
      (rtl:reduce-subparts expression + 0 loop
	(lambda (object)
	  (cond ((integer? object) (inexact->exact object))
		((symbol? object) (symbol-hash object))
		((string? object) (string-hash object))
		(else (hash-object object))))))

    (let ((hash (loop expression)))
      (receiver (modulo hash (rcse-ht-size))
		do-not-record?
		hash-arg-in-memory?))))

;;;; Table Search

(define (find-cheapest-expression expression hash volatile?)
  ;; Find the cheapest equivalent expression for EXPRESSION.
  (let ((element (find-cheapest-valid-element expression hash volatile?)))
    (if element
	(element-expression element)
	expression)))

(define (find-cheapest-valid-element expression hash volatile?)
  ;; Find the cheapest valid hash table element for EXPRESSION.
  ;; Returns false if no such element exists or if EXPRESSION is
  ;; VOLATILE?.
  (and (not volatile?)
       (let ((element (rcse-ht-lookup hash expression)))
	 (and element
	      (let ((element* (element-first-value element)))
		(if (eq? element element*)
		    element
		    (let loop ((element element*))
		      (and element
			   (let ((expression (element-expression element)))
			     (if (or (rtl:register? expression)
				     (expression-valid? expression))
				 element
				 (loop (element-next-value element))))))))))))

(define (expression-valid? expression)
  ;; True iff all registers mentioned in EXPRESSION have valid values
  ;; in the hash table.
  (if (rtl:register? expression)
      (let ((register (rtl:register-number expression)))
	(= (register-in-table register) (register-tick register)))
      (rtl:all-subexpressions? expression expression-valid?)))

(define (element->class element)
  ;; Return the cheapest element in the hash table which has the same
  ;; value as `element'.  This is necessary because `element' may have
  ;; been deleted due to register or memory invalidation.
  (and element
       ;; If `element' has been deleted from the hash table,
       ;; `element-first-value' will be false.  [ref crock-1]
       (or (element-first-value element)
	   (element->class (element-next-value element)))))

;;;; Insertion

(define (insert-register-destination! expression element)
  ;; Insert EXPRESSION, which should be a register expression, into
  ;; the hash table as the destination of an assignment.  ELEMENT is
  ;; the hash table element for the value being assigned to
  ;; EXPRESSION.
  (let ((register (rtl:register-number expression)))
    (set-register-expression! register expression)
    (let ((quantity (get-element-quantity element)))
      (if quantity
	  (begin
	    (set-register-quantity! register quantity)
	    (let ((last (quantity-last-register quantity)))
	      (cond ((not last)
		     (set-quantity-first-register! quantity register)
		     (set-register-next-equivalent! register false))
		    (else
		     (set-register-next-equivalent! last register)
		     (set-register-previous-equivalent! register last))))
	    (set-quantity-last-register! quantity register)))))
  (set-element-in-memory?! (rcse-ht-insert! (expression-hash expression)
					    expression
					    (element->class element))
			   false))

(define (insert-stack-destination! expression element)
  (let ((quantity (get-element-quantity element)))
    (if quantity
	(set-stack-reference-quantity! expression quantity)))
  (set-element-in-memory?! (rcse-ht-insert! (expression-hash expression)
					    expression
					    (element->class element))
			   false))

(define (get-element-quantity element)
  (let loop ((element (element->class element)))
    (and element
	 (let ((expression (element-expression element)))
	   (cond ((rtl:register? expression)
		  (get-register-quantity (rtl:register-number expression)))
		 ((stack-reference? expression)
		  (stack-reference-quantity expression))
		 (else
		  (loop (element-next-value element))))))))

(define (insert-memory-destination! expression element hash)
  (let ((class (element->class element)))
    (mention-registers! expression)
    ;; Optimization: if class and hash are both false, rcse-ht-insert!
    ;; makes an element which is not connected to the rest of the table.
    ;; In that case, there is no need to make an element at all.
    (if (or class hash)
	(set-element-in-memory?! (rcse-ht-insert! hash expression class)
				 true))))

(define (mention-registers! expression)
  (if (rtl:register? expression)
      (let ((register (rtl:register-number expression)))
	(remove-invalid-references! register)
	(set-register-in-table! register (register-tick register)))
      (rtl:for-each-subexpression expression mention-registers!)))

(define (remove-invalid-references! register)
  ;; If REGISTER is invalid, delete from the hash table all
  ;; expressions which refer to it.
  (if (let ((in-table (register-in-table register)))
	(and (not (negative? in-table))
	     (not (= in-table (register-tick register)))))
      (let ((expression (register-expression register)))
	(rcse-ht-delete-class!
	 (lambda (element)
	   (let ((expression* (element-expression element)))
	     (and (not (rtl:register? expression*))
		  (expression-refers-to? expression* expression)))))))
  unspecific)

;;;; Invalidation

(define (non-object-invalidate!)
  (rcse-ht-delete-class!
   (lambda (element)
     (not (rtl:object-valued-expression? (element-expression element))))))

(define (varying-address-invalidate!)
  (rcse-ht-delete-class!
   (lambda (element)
     (and (element-in-memory? element)
	  (expression-address-varies? (element-expression element))))))

(define (expression-invalidate! expression)
  ;; Delete from the table any expression which refers to this
  ;; expression.
  (if (rtl:register? expression)
      (register-expression-invalidate! expression)
      (rcse-ht-delete-class!
       (lambda (element)
	 (expression-refers-to? (element-expression element) expression)))))

(define (register-expression-invalidate! expression)
  ;; Invalidate a register expression.  These expressions are handled
  ;; specially for efficiency -- the register is marked invalid but we
  ;; delay searching the hash table for relevant expressions.
  (let ((register (rtl:register-number expression))
	(hash (expression-hash expression)))
    (register-invalidate! register)
    ;; If we're invalidating the stack pointer, delete its entries
    ;; immediately.
    (if (interpreter-stack-pointer? expression)
	(mention-registers! expression)
	(rcse-ht-delete! hash (rcse-ht-lookup hash expression)))))

(define (register-invalidate! register)
  (let ((next (register-next-equivalent register))
	(previous (register-previous-equivalent register))
	(quantity (get-register-quantity register)))
    (set-register-tick! register (1+ (register-tick register)))
    (if next
	(set-register-previous-equivalent! next previous)
	(set-quantity-last-register! quantity previous))
    (if previous
	(set-register-next-equivalent! previous next)
	(set-quantity-first-register! quantity next))
    (set-register-quantity! register (new-quantity register))
    (set-register-next-equivalent! register false)
    (set-register-previous-equivalent! register false))
  unspecific)