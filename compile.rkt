#lang racket

(require parser-tools/private-lex/re
         parser-tools/private-lex/deriv
         parser-tools/private-lex/util
         (prefix-in mz: mzlib/integer-set)
         racket/unsafe/ops
         (for-syntax racket
                     racket/unsafe/ops
                     (prefix-in mz: mzlib/integer-set))
         (for-template racket
                       racket/unsafe/ops))

(provide (combine-out compile-dfa build-test-dfa
                      (all-from-out parser-tools/private-lex/re)
                      (all-from-out parser-tools/private-lex/deriv)))

(define (dispatched x) (integer->char x))

(define-struct state (name [final? #:mutable] [edges #:mutable]))
;; where name : syntax?, final? : boolean?, transitions : (list-of edge?)

(define-struct edge (range))		;; where range : (cons-of number? number?)
(define-struct error-edge edge ())
(define-struct trans-edge edge (goto))	;; where goto : state

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; From Deriv-Racket
;; (make-dfa num-states start-state final-states/actions transitions)
;;  where num-states, start-states are int
;;  final-states/actions is (list-of (cons int syntax-object))
;;  transitions is (list-of (cons int (list-of (cons char-set int))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; "accessor" functions for data structures used by deriv
(define transition-state-id car)
(define transition-list cdr)
(define final-state-id car)

;; Combines two lists of edges, assuming that (1) they are disjoint
;; and (2) each list is sorted
(define (merge elist1 elist2)
  (define (merge-acc el1 el2 acc)
    (match* (el1 el2)
      [('() _) (append (reverse acc) el1)]
      [(_ '()) (append (reverse acc) el2)]
      [((cons e1 el1') (cons e2 el2'))
       (if (< (car (edge-range e1)) (car (edge-range e2)))
	   (merge-acc el1' el2 (cons e1 acc))
	   (merge-acc el1 el2' (cons e2 acc)))]))
  (merge-acc elist1 elist2 '()))

;; Converts representation of transitions from deriv's (which uses a
;; list of charsets) to ours (a flattened list of edges), given a
;; state vector `states'
(define (transitions->edges states transitions)
  (let-values 
      ([(good-chars edge-list) 
	(for/fold ([good-chars (mz:make-range)]
		   [edge-list  '()])
	          ([transition (in-list transitions)])
	  (match-let ([(cons char-set goto-state-id) transition])
	    (values (mz:union good-chars char-set)
		    (merge (map (trans-edge _ (vector-ref states goto-state-id))
				(mz:integer-set-contents char-set))
			   edge-list))))])
    (merge (map error-edge (mz:integer-set-contents (mz:complement good-chars)))
	   edge-list)))

;; Transforms the dfa representation (which has lists of transitions
;; and actions indexed by state id) to a flat vector of state
;; structures, each containing all information relevant to a state.

;; collate-states : dfa? -> (vector-of state?)  
(define (collate-states dfa)
  (let ([states (for/vector ([i (in-range (dfa-num-states dfa))])
		  (state (generate-temporary (format "state-~a" i)) #f '()))])

    ; load the dfa's transitions into each state, via mutation
    (for ([t (in-list (dfa-transitions dfa))])
       (set-state-transitions (vector-ref (transition-state-id t))
			      (transitions->edges states (transition-list t))))

    ; record the dfa's final states, again via mutation
    (for ([f (in-list (dfa-final-states/actions dfa))])
      (set-state-final? (vector-ref states (final-state-id f) #t)))

    states)

(define (compile-state input-string-stx input-len-stx end*? st)
  (match-let ([(state name-stx final? edges) st]
	      [char-stx (generate-temporary 'char)]
	      [pos-stx  (generate-temporary 'pos)])
    (with-syntax ([name         name-stx]
		  [input-string input-string-stx]
		  [input-len    input-len-stx]
		  [char         char-stx]
		  [pos		pos-stx])
      (if (and final? end*?)
	  #'[name (lambda (pos) #t)]
	  #`[name (lambda (pos)
		    (if (unsafe-fx= pos input-len)
			#,final?
			(let ([char (unsafe-string-ref input-string pos)])
			  #,(compile-dispatch final? edges char-stx pos-stx))))]))))

(define (compile-dispatch final? edges char-stx pos-stx)
  (match-let* ([part-ref (quotient (length rmaps) 2)]  
	       [(cons (range low hi) going) (list-ref rmaps part-ref)]
	       [(cons less more) (list-rmaps->partitions rmaps low)])
    (with-syntax* ([dest going] 
		   [l (dispatched low)] 
		   [h (dispatched hi)]
		   [next #'(unsafe-fx+ i 1)]
		   [this-range
		      (if (singleton? (car part))
			  #'(and (unsafe-fx= n l) (dest next))
			  #'(and (unsafe-fx<= n h)
				 (unsafe-fx>= n l)
				 (dest next)))])
	 (match* (less more)
	   [('() '()) #'this-range]
	   [('() _)   #`(if (unsafe-fx> n h) #,(build-bst more) this-range)]
	   [(_   '()) #`(if (unsafe-fx< n l) #,(build-bst less) this-range)]
	   [(_   _)   #`(cond [(unsafe-fx> n h) #,(build-bst more)]
			      [(unsafe-fx< n l) #,(build-bst less)]
			      [else (dest next)])]))))

;; (: compile-fa (dfa? boolean? -> SYNTAX))
(define (compile-dfa dfa end*?)
  (unless (dfa? dfa) (error 'dfa-epxand "expected a dfa given: ~s" dfa))
  (let* ([input-string-stx (generate-temporary 'input-string)]  
         [input-len-stx    (generate-temporary 'input-len)])
    (with-syntax ([(nodes ...) 
		   (for/list ([st (in-vector (collate-states dfa))])
		     (trans-expand input-string-stx input-len-stx end*? st))]
                  [input-string input-string-stx] 
		  [input-len    input-len-stx]
                  [start (id-of (dfa-start-state in))])
      #'(lambda (input-string)
          (let ([input-len (string-length string)])
	    (letrec (nodes ...)
	      (start 0)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For output / testing

(define (build-and-print x)
  (print-dfa (build-test-dfa x)))

(define (build-test-dfa rs)
  (let ((c (make-cache)))
    (build-dfa (map (lambda (x) (cons (->re x c) 'action))
                    rs)
               c)))