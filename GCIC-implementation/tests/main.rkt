#lang racket

(require rackunit)
(require "../main.rkt")
(require (except-in "../elaboration.rkt"
                    check))
(require "../evaluation.rkt")
(require "../syntax.rkt")
(require "../examples.rkt")

(unsafe-optimize? #t)

(define defs (parse-defs `(,ind-def-nat
                           ,ind-def-bool
                           ,ind-def-unit
                           ,ind-def-void
                           ,ind-def-eq-nat
                           ,ind-def-list
                           ,ind-def-list-1-weird
                           ,ind-def-vec-f
                           ,ind-def-fin-f)))

(define-simple-check (check-program prog expected defs)
  (=α (run prog)
      (parse-term expected defs)))

(define-simple-check (check-program-consistent prog expected defs)
  (~α (run prog)
      (parse-term expected defs)))

(check-program prog-add-2-3 (encode-nat 5) defs)

(check-program prog-leb-2-3 '(@ Bool true &) defs)

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
(check-program prog-list-univ-weird
               '(@ List1^ cons (□ 0) & (Nat)
                  (@ List1^ null (□ 0) &))
               defs)

(define bad-prog-list-append
  `(,default-variant
    ,ind-def-nat
    ,ind-def-list
    (((,fun-append (Nat))
      ,(encode-list-nat '(1 2)))
     ,(encode-nat 3))))

(check-exn #rx"^check:" (λ () (run bad-prog-list-append)))

(check-program prog-list-length-123 (encode-nat 3) defs)

(check-program prog-vec-f-12
               (encode-vec-f-nat '(1 2))
               defs)

#;
(check-program prog-vec-f-append-12-34
               (encode-vec-f-nat '(1 2 3 4))
               defs)

(check-program prog-head-f (encode-nat 42) defs)
(check-program-consistent
   prog-vec-f-filter-leb4-35 (encode-vec-f-nat '(3)) defs)

(check-program-consistent prog-example-1 (encode-nat 3) defs)
(check-program prog-example-1-err '(err (Nat)) defs)

(check-program prog-compose-≤3-length-123 '(@ Bool true &) defs)
(parameterize ([trace-eval? #f])
  (check-program prog-blame '(err (Nat)) defs))

#;
(check-program prog-nth-1-34 (encode-nat 4) defs)

;; Takes too long to run
#;
(check-program prog-nth-3-1234 (encode-nat 4) defs)
