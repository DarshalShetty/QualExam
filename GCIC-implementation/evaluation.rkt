#lang racket

(require (only-in "syntax.rkt"
                  supported-variants
                  Var Univ App Lam Pi IndT Constr IndElim
                  Unk Err Cast
                  get-params debug-log
                  ))
(provide (all-defined-out))

(define current-variant (make-parameter #f))
(define (set-variant! variant^)
  (cond
    [(memv variant^ supported-variants) (current-variant variant^)]
    [else (error 'set-variant
                 "Variant '~a' not supported. Expected one of ~a"
                 variant^ supported-variants)]))


(define (sΠ i j)
  (match (current-variant)
    [(or 'gcic-g 'gcic-n) (max i j)]
    ['gcic-shift (add1 (max i j))]))

(define (cΠ i)
  (match (current-variant)
    [(or 'gcic-n 'gcic-shift) (sub1 i)]
    ['gcic-g i]))

(struct Head () #:transparent)
(struct HeadPi Head () #:transparent)
(struct HeadUniv Head (level) #:transparent)
(struct HeadIndT Head (name) #:transparent)

;; precondition: (ccic-term? t)
;; postcondition: (Head? (head t))
(define (head t)
  (match t
    [(Pi _ _ _) (HeadPi)]
    [(Univ l) (HeadUniv l)]
    [(IndT name _ _) (HeadIndT name)]
    [_ (error 'head "Expected a CastCIC type, but got: ~a" t)]))

;; precondition: (and (Head? hd)
;;                    (natural? level)
;;                    (*cic-defs? ccic-term? defs))
;; postcondition: (ccic-term? (germ hd level defs))
(define (germ hd level defs)
  (match hd
    [(HeadUniv j) #:when (< j level) (Univ j)]
    [(HeadUniv j) (Err (Univ level))]
    [(HeadIndT name)
     (IndT name level (map (λ (p) (Unk p)) (get-params defs name level)))]
    [(HeadPi)
     #:when (>= (cΠ level) 0)
     (Pi '_ (Unk (Univ (cΠ level))) (Unk (Univ (cΠ level))))]
    [(HeadPi) (Err (Univ level))]))

(define (germ? term level)
  (match term
    [(or (Univ i) (Err (Univ i)))
     #:when (eqv? i level)
     #t]
    [(Pi _ (Unk (Univ i)) (Unk (Univ i)))
     #:when (and (> (cΠ level) 0) (eqv? i (cΠ level)))
     #t]
    [(IndT _ i params)
     #:when (eqv? i level)
     (for/and ([param params])
       (match param
         [(Unk _) #t]
         [_ #f]))]
    [_
     (debug-log (format "Not a germ at level ~a: ~a" level term))
     #f]))

;; Preconditons: (ccic-term? term)
(define (canonical-term? term)
  (match term
    [(or (Lam _ _ _)
         (Constr _ _ _ _ _)
         (Pi _ _ _)
         (Univ _)
         (IndT _ _ _))
     #t]
    [(or (Unk t) (Err t))
     (match t
       [(or (Univ _)
            (IndT _ _ _)
            (Unk (Univ _))
            (Err (Univ _)))
        #t]
       [_
        (define-values (term-struct _) (struct-info t))
        (define-values (term-name _1 _2 _3 _4 _5 _6 _7) (struct-type-info term-struct))
        (debug-log (format "Invalid type associated with term ~a: ~a" term-name t))
        #f])]
    [(Cast term source (Unk (Univ level)))
     #:when (germ? source level)
     #t]
    [_ (neutral-term? term)]))

;; Preconditons: (ccic-term? term)
(define (neutral-term? term)
  (match term
    [(Var _) #t]
    [(App rator _) (neutral-term? rator)]
    [(IndElim _ scrut _ _ _ _) (neutral-term? scrut)]
    [(or (Unk t) (Err t)) (neutral-term? t)]
    [(Cast source target term)
     (match source
       [(Unk (Univ _)) (neutral-term? term)]
       [(Univ _) (neutral-term? target)]
       [(Pi _ _ _)
        (match target
          [(Pi _ _ _) (neutral-term? term)]
          [_ (neutral-term? target)])]
       [(IndT _ _ _)
        (match target
          [(IndT _ _ _) (neutral-term? term)]
          [_ (neutral-term? target)])]
       [_ (neutral-term? source)])]
    [_
     (debug-log (format "Not a neutral term: ~a" term))
     #f]))

; ∃ scope, defs . (and (ccic-term? term defs scope)
;                      (ccic-term? (reduce-principal term) defs scope))
(define (reduce-principal term)
  (match term
    [_ (error 'reduce-principal "TODO: not implemented")]))
