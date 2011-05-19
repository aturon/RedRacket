#lang racket

;; todo: contracts

(require parser-tools/private-lex/re
         parser-tools/private-lex/deriv
         parser-tools/private-lex/util
         (prefix-in mz: mzlib/integer-set)
         racket/unsafe/ops
         unstable/syntax
         "fancy-app.rkt"
         (for-syntax racket
                     racket/unsafe/ops
                     (prefix-in mz: mzlib/integer-set))
         (for-template racket/base
                       racket/unsafe/ops))

(provide (combine-out compile-dfa build-test-dfa
                      (all-from-out parser-tools/private-lex/re)
                      (all-from-out parser-tools/private-lex/deriv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; INTERNAL REPRESENTATION OF DFA STATES: A VECTOR OF STATE STRUCTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct state (name [final? #:mutable] [edges #:mutable]))
;; where name : syntax?, final? : boolean?, transitions : (list-of edge?)

(struct edge (range))		;; where range : (cons-of number? number?)
(struct error-edge edge ())
(struct trans-edge edge (goto))	;; where goto : state

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CONVERSION FROM DERIV'S DFA REPRESENTATION TO OURS:
;;
;; deriv's representation is:
;;   (make-dfa num-states start-state final-states/actions transitions)
;;    where num-states, start-states are int
;;    final-states/actions is (list-of (cons int syntax-object))
;;    transitions is (list-of (cons int (list-of (cons char-set int))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; "accessor" functions for data structures used by deriv
(define transition-state-id car)
(define transition-list cdr)
(define final-state-id car)

;; todo -- letloop
;; Combines two (lists-of edge?), assuming that (1) they are disjoint
;; and (2) each list is sorted, returning a sorted list
(define (merge elist1 elist2)
  (define (merge-acc el1 el2 acc)
    (match* (el1 el2)
      [('() _) (append (reverse acc) el1)]
      [(_ '()) (append (reverse acc) el2)]
      [((cons e1 el1-rest) (cons e2 el2-rest))
       (if (< (car (edge-range e1)) (car (edge-range e2)))
	   (merge-acc el1-rest el2 (cons e1 acc))
	   (merge-acc el1 el2-rest (cons e2 acc)))]))
  (merge-acc elist1 elist2 '()))

;; Converts representation of transitions from deriv's (which uses a
;; list of charsets) to ours (a flattened list of edges), given a
;; state vector `states'
(define (transitions->edges states transitions)
  (define-values (good-chars edge-list) 
    (for/fold ([good-chars (mz:make-range)]
	       [edge-list  '()])
	      ([transition (in-list transitions)])
      (match-define (cons char-set goto-state-id) transition)
      (values (mz:union good-chars char-set)
	      (merge (map (trans-edge _ (vector-ref states goto-state-id))
			  (mz:integer-set-contents char-set))
		     edge-list))))
  (merge (map error-edge (mz:integer-set-contents (mz:complement good-chars)))
	 edge-list))

;; Transforms the dfa representation (which has lists of transitions
;; and actions indexed by state id) to a flat vector of state
;; structures, each containing all information relevant to a state.

;; collate-states : (dfa? -> (vector-of state?))
(define (collate-states dfa)
  (define states (for/vector ([i (in-range (dfa-num-states dfa))])
		  (state (generate-temporary (format "state-~a" i)) #f '())))
  (for ([t (in-list (dfa-transitions dfa))])
     (set-state-edges! (vector-ref (transition-state-id t))
		       (transitions->edges states (transition-list t))))
  (for ([f (in-list (dfa-final-states/actions dfa))])
     (set-state-final?! (vector-ref states (final-state-id f) #t)))
  states)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DFA COMPILATION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binary-search-cutoff 10)

;; produces syntax for dispatching a list of edges, given that (at
;; template time) char-stx is bound to the character read and pos-stx
;; is bound to the current position
(define (compile-dispatch edges char-stx pos-stx) 
  (define/with-syntax (char pos) (list char-stx pos-stx))
  (define (dispatch-stx edges)
    (if (< (length edges) binary-search-cutoff) 
	(scan-stx edges) 
	(binary-search-stx edges)))
  (define (binary-search-stx edges)   ; precondition: (> (length edges) 2)
    (define-values (edges-low edges-high)
      (split-at edges (quotient (length edges) 2)))
    (define boundary (car (edge-range (car edges-high))))
    #`(if (unsafe-fx< char #,boundary)
	  #,(dispatch-stx edges-low)
	  #,(dispatch-stx edges-high)))
  (define (scan-stx edges)     ; precondition: (> (length edges) 0)
    (define/with-syntax (cond-clause ...)
      (for/list ([edge (in-list edges)])
        (define/with-syntax body
	  (match edge 
	    [(trans-edge _ goto) #`(#,goto (unsafe-fx+ 1 pos))]
	    [(error-edge _)      #'#f]))
	#`[(unsafe-fx<= char #,(cdr (edge-range edge))) body]))
    #'(cond (cond-clause ...)))
  (dispatch-stx edges))

;; produces syntax for a state, as a letrec clause, assuming that
;; input-string-stx and input-len-stx are bound at template time
(define (compile-state input-string-stx input-len-stx end*? st)
  (define-match (state name-stx final? edges) st)
  (define/with-syntax (name input-string input-len)
    (name-stx input-string-stx input-len-stx))
  (define/with-syntax (char pos) (generate-temporaries '(char pos)))
  (if (and final? end*?)
      #'[name (lambda (pos) #t)]
      #`[name (lambda (pos)
		(if (unsafe-fx= pos input-len)
		    #,final?
		    (let ([char (unsafe-string-ref input-string pos)])
		      #,(compile-dispatch edges #'char #'pos))))]))

;; compile-dfa : (dfa? boolean? -> syntax?)
(define (compile-dfa dfa end*?)
  (define states (collate-states dfa))
  (define/with-syntax (input-string input-len) 
    (generate-temporaries '(input-string, input-len)))
  (define/with-syntax (nodes ...) 
    (for/list ([st (in-vector states)])
      (compile-state #'input-string #'input-len end*? st)))
  (define/with-syntax start-state
    (state-name (vector-ref states (dfa-start-state in))))
  #'(lambda (input-string)
      (let ([input-len (string-length string)])
	(letrec (nodes ...)
	  (start-state 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For output / testing

(define (build-and-print x)
  (print-dfa (build-test-dfa x)))

(define (build-test-dfa rs)
  (let ((c (make-cache)))
    (build-dfa (map (lambda (x) (cons (->re x c) 'action))
                    rs)
               c)))