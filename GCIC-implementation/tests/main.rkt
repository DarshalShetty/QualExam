#lang racket

(require rackunit)
(require "../main.rkt")
(require (except-in "../elaboration.rkt"
                    check))
(require "../evaluation.rkt")
(require "../syntax.rkt")
(require "../examples.rkt")

(define defs (parse-defs `(,ind-def-nat
                           ,ind-def-unit
                           ,ind-def-void
                           ,ind-def-eq-nat
                           ,ind-def-list
                           ,ind-def-vec-f)))

(define-simple-check (check-program prog expected defs)
  (=α (run prog #:force? #t)
      (parse-term expected defs)))

(check-program prog-add-2-3 (encode-nat 5) defs)

(check-program prog-eq-nat-2
               '(@
                 EqNat
                 refl-nat
                 (@ Nat succ & (@ Nat succ & (@ Nat zero &)))
                 (@ Nat succ & (@ Nat succ & (@ Nat zero &)))
                 &
                 (@ Unit tt &))
               defs)

(check-program prog-list-append-12-34
               (encode-list-nat '(1 2 3 4))
               defs)

(define bad-prog-list-append
  `(,default-variant
    ,ind-def-nat
    ,ind-def-list
    (((,fun-append (Nat))
      ,(encode-list-nat '(1 2)))
     ,(encode-nat 3))))

(check-exn #rx"^check:" (λ () (run bad-prog-list-append #:force? #t)))

(check-program prog-vec-12
               (encode-vec-nat '(1 2))
               defs)
