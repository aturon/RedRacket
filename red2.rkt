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

(provide (combine-out dfa-expand build-test-dfa
                      (all-from-out parser-tools/private-lex/re)
                      (all-from-out parser-tools/private-lex/deriv)))

(define (dispatched x) (integer->char x))

(define-struct state (name [final? #:mutable] [edges #:mutable]))
;; where name : syntax?, final? : boolean?, transitions : (list-of edge?)

(define-struct range (from to))
;; where from, to : number

(define-struct edge (rng))
;; where rng : range

(define-struct error-edge edge ())
(define-struct trans-edge edge (goto))
;; where goto : state

(define (trans-expand input-string-stx input-len-stx end*? st)
  (match-let ([(state name-stx final? transitions) st]
	      [pos-stx  (generate-temporary 'pos)]
	      [char-stx (generate-temporary 'char)])
    (with-syntax ([name         name-stx]
		  [input-string input-string-stx]
		  [input-len    input-len-stx]
		  [pos          pos-stx]
		  [char         char-stx]
		  [fall-thru    final?])
      #`[name (lambda (pos) 
		#,(if (and final? end*?) 
		      #'#t 
		      (dispatch ...)))])))

;; (: dispatch-one (temporary boolean (Listof RangeMapping) -> SYNTAX))
(define (dispatch-one state final? rmaps)
  (if (null? rmaps) final?
      (if (and final? (or fast-stop? (staying-here? rmaps state)))
          #f
	  (build-bst rmaps))))

;; (: staying-here? ((Listof RangeMapping) Temporary -> Boolena))
(define (staying-here? rmaps id) 
  (andmap (lambda (pair) (bound-identifier=? (cdr pair id))) rmaps))

;---at--- use split-at
;; (: list-rmaps->partition ((Listof RangeMapping) Number)
;;       -> (Pair (Listof RangeMapping) (Listof RangeMapping)))
(define (list-rmaps->partitions rmaps part)
  (let loop ([rmaps rmaps] [acc null])
    (if (null? rmaps) 
	(cons (reverse acc) null)
        (let ([start (range-min (caar rmaps))])
          (cond [(< start part) (loop (cdr rmaps) (cons (car rmaps) acc))]
                [(= start part) (loop (cdr rmaps) acc)]
                [else (cons (reverse acc) rmaps)])))))

;; (: build-bst ((Listof RangeMapping) -> SYNTAX))
(define (build-bst rmaps)
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

(define (merge tlist1 tlist2)
  (define (merge-acc tl1 tl2 acc)
    (match* (tl1 tl2)
      [('() _) (append (reverse tl2) acc)]
      [(_ '()) (append (reverse tl1) acc)]
      [((cons e1 tl1') (cons e2 tl2'))
       (if (< (range-low (edge-rng e1)) (range-low (edge-rng e2)))
	   (merge-acc tl1' tl2 (cons e1 acc))
	   (merge-acc tl1 tl2' (cons e2 acc)))]))
  (merge-acc tlist1 tlist2 '()))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; From Deriv-Racket
;; (make-dfa num-states start-state final-states/actions transitions)
;;  where num-states, start-states are int
;;  final-states/actions is (list-of (cons int syntax-object))
;;  transitions is (list-of (cons int (list-of (cons char-set int))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Transforms the dfa representation (which has lists of transitions
;; and actions indexed by state id) to a flat vector of state
;; structures, each containing all information relevant to a state.

;; collate-states : dfa? -> (vector-of state?)  
(define (collate-states dfa)
  (let* ([states (for/vector ([i (in-range (dfa-num-states dfa))])
  		   (state (generate-temporary (string-append "state-" (number->string i)))
			  #f 
			  '()))]
	 [flatten 
	  (lambda (transitions)
	    (for/fold ([good-chars (mz:make-range)]
		       [flattened  '()])
		      ([transition (in-list transitions)])
	      (match-let ([(cons char-set goto-state-id) transition])
		(values (mz:union good-chars char-set)
			(merge (map (lambda (rng)
				      (trans-edge (range (car rng) (cdr rng))
						  (vector-ref states goto-state-id)))
				    (mz:integer-set-contents char-set))
			       flattened)))))]
	 [transtions->edges 
	  (lambda (transitions)
	    (let-values ([(good-chars edge-list)] (flatten transitions))
	      (merge (map (lambda (rng) (error-edge (range (car rng) (cdr rng))))
			  (mz:integer-set-contents (mz:complement good-chars)))
		     edge-list)))])

    ; load in the dfa's transitions to each state, via mutation
    (for-each (match-lambda [(cons state-id transitions) 
			     (set-state-transitions (vector-ref state-id)
						    (transitions->edges transitions))])
	      (dfa-transitions dfa))

    ; record the dfa's final states, again via mutation
    (for-each (match-lambda [(cons state-id _) 
			     (set-state-final? (vector-ref states state-id) #t)]) 
	      (dfa-final-states/actions dfa))

    states))

;; (: dfa-expand (dfa -> SYNTAX))
(define (dfa-expand dfa end*?)
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