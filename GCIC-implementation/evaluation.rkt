#lang racket

(require (only-in "syntax.rkt"
                  supported-variants
                  Var Univ App Lam Pi IndT Constr IndElim
                  Unk Err Cast
                  get-params
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

;; Preconditons: (ccic-term? term) = #t
(define (canonical-term? term)
  (error 'canonical-term? "TODO: not implemented"))

;; Preconditons: (ccic-term? term) = #t
(define (neutral-term? term)
  (error 'neutral-term? "TODO: not implemented"))
