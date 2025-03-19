#lang racket

(define (sΠ i j)
  (error 'sΠ "not implemented"))

(define (cΠ i j)
  (error 'cΠ "not implemented"))

(define-struct HeadPi () #:transparent)
(define-struct HeadUniv (level) #:transparent)
(define-struct HeadInd () #:transparent)

(define (germ hd level defs)
  (error 'germ "not implemented"))

;; Preconditons: (ccic-term? term) = #t
(define (canonical-term? term)
  (error 'canonical-term? "not implemented"))

;; Preconditons: (ccic-term? term) = #t
(define (neutral-term? term)
  (error 'neutral-term? "not implemented"))
