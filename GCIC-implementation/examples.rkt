#lang racket

(provide (all-defined-out))

(define default-variant
  '(variant gcic-n))

(define ind-def-nat
  '(data Nat
         ((zero)
          (succ (_ : (Nat))))))

(define (encode-nat n)
  (for/fold ([res '(@ Nat zero &)])
            ([_ (in-range n)])
    `(@ Nat succ & ,res)))

(define fun-add
  '(λ (m : (Nat))
     (λ (n : (Nat))
       (elim Nat n as (λ (_) (Nat)) rec succ-app with
             [(zero) => m]
             [(succ n) => (@ Nat succ & (succ-app n))]))))

(define ind-def-unit
  '(data Unit
         ((tt))))

(define ind-def-void
  '(data Void
         ()))

(define ind-def-eq-nat
  '(data EqNat (n1 : (Nat)) (n2 : (Nat))
         ((refl-nat (_ : ((elim Nat n1 as (λ (_) (Π (_ : (Nat)) (□ 0))) rec f1 with
                               [(zero) => (λ (n2 : (Nat))
                                            (elim Nat n2 as (λ (_) (□ 0)) rec _ with
                                                  [(zero) => (Unit)]
                                                  [(succ _) => (Void)]))]
                               [(succ n1^)
                                =>
                                (λ (n2 : (Nat))
                                  (elim Nat n2 as (λ (_) (□ 0)) rec _ with
                                        [(zero) => (Void)]
                                        [(succ n2^) => ((f1 n1^) n2^)]))])
                          n2))))))

(define ind-def-bool
  '(data bool
         ((true)
          (false))))

(define ind-def-list
  `(data List (A : (□ 0))
         ([null]
          [cons (_ : A) (_ : (List A))])))

(define (encode-list-nat ls)
  (for/foldr ([res '(@ List null (Nat) &)])
             ([l ls])
    `(@ List cons (Nat) & ,(encode-nat l) ,res)))

(define prog-nat-one
  `(,default-variant
    ,ind-def-nat
    ,(encode-nat 1)))

(define prog-list-nat-one
  `(,default-variant
    ,ind-def-nat
    ,ind-def-list
    (@ List cons (Nat) & ,(encode-nat 1)
       (@ List null (Nat) &))))

(define fun-append
  '(λ (A : (□ 0))
     (λ (l1 : (List A))
       (λ (l2 : (List A))
         (elim List l1 as (λ (_) (List A)) rec append-l2 with
               [(null) => l2]
               [(cons hd tl) => (@ List cons A & hd (append-l2 tl))])))))

(define prog-list-append-12-34
  `(,default-variant
    ,ind-def-nat
    ,ind-def-list
    (((,fun-append (Nat))
      ,(encode-list-nat '(1 2)))
     ,(encode-list-nat '(3 4)))))

(define ind-def-vec-f
  `(data VecF (A : (□ 0)) (n : (Nat))
         ((nil-f (_ : (EqNat ,(encode-nat 0) n)))
          (cons-f (_ : A)
                  (m : (Nat))
                  (_ : (EqNat (@ Nat succ & m) n))
                  (_ : (VecF A m))))))

(define fun-vec-f-append
  `(λ (A : (□ 0))
     (λ (m : (Nat))
       (λ (n : (Nat))
         (λ (v1 : (VecF A m))
           (λ (v2 : (VecF A n))
             (elim VecF v1 as (λ (_) (VecF A ((,fun-add m) n))) rec append-v2 with
                   [(nil-f eq-0-m) => v2]
                   [(cons-f hd m^ eq-Sm^-m tl) =>
                    (@ VecF cons-f A (? 0) & hd (? 0) (? 0) (append-v2 tl))])))))))

(define (encode-vec-f-nat ls)
  (for/foldr ([result `(@ VecF nil-f (Nat) ,(encode-nat 0) &
                          (@ EqNat refl-nat ,(encode-nat 0) ,(encode-nat 0) &
                             (@ Unit tt &)))]
              [size 0]
              #:result result)
             ([n ls])
    (define out-size (add1 size))
    (values
     `(@ VecF cons-f (Nat) ,(encode-nat out-size)
              & ,(encode-nat n) ,(encode-nat size)
              (@ EqNat refl-nat ,(encode-nat out-size) ,(encode-nat out-size)
                       & (@ Unit tt &))
              ,result)
     out-size)))

(define term-vec-f-12
  (encode-vec-f-nat '(1 2)))

(define prog-vec-f-12
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,ind-def-vec-f
    ,term-vec-f-12))

(define prog-vec-f-append-12-34
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,ind-def-vec-f
    (((((,fun-vec-f-append (Nat))
        ,(encode-nat 2))
       ,(encode-nat 2))
      ,term-vec-f-12)
     ,(encode-vec-f-nat '(3 4)))))

(define ind-def-prod
  `(data Prod (A : (□ 0)) (B : (□ 0))
         ([pair (_ : A) (_ : B)])))

(define fun-vec-μ
  `(λ (A : (□ 0))
     (λ (n : (Nat))
       (elim Nat n as (λ (_) (□ 0)) rec r with
             [(zero) => (Unit)]
             [(succ n^) => (Prod A (r n^))]))))

(define (type-vec-μ A n)
  `((,fun-vec-μ ,A) ,(encode-nat n)))

(define fun-nil-μ
  `(λ (A : (□ 0))
      (@ Unit tt &)))

(define fun-cons-μ
  `(λ (A : (□ 0))
     (λ (a : A)
       (λ (n : (Nat))
         (λ (v : ((,fun-vec-μ A) n))
           (@ Prod pair A ((,fun-vec-μ A) n) & a v))))))

(define (encode-vec-μ-nat ls)
  (for/foldr ([result `(,fun-nil-μ (Nat))]
              [size 0]
              #:result result)
             ([n ls])
    (values
     `((((,fun-cons-μ (Nat)) ,(encode-nat n)) ,(encode-nat size)) ,result)
     (add1 size))))

(define term-check-arg
  `((λ (a : (Prod ((λ (A : (□ 0)) A) (Nat)) (Nat))) a)
    (@ Prod pair (Nat) (Nat) & ,(encode-nat 0) ,(encode-nat 0))))

(define prog-check-arg
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-prod
    ,term-check-arg))

(define prog-vec-μ-12
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-prod
    ,(encode-vec-μ-nat '(1 2))))

(define prog-omega
  `(,default-variant
    ((λ (x : (? 1)) (x x)) (λ (x : (? 1)) (x x)))))

(define prog-scope
  `(,default-variant
     (λ (X : (□ 0))
       (λ (f : (Π (_ : X) X))
         (λ (X : (□ 0))
           (λ (x : X)
             (f x)))))))

(define term-two
  (encode-nat 2))
(define term-three
  (encode-nat 3))

(define prog-add-2-3
  `(,default-variant
    ,ind-def-nat
    ((,fun-add ,term-two) ,term-three)))

(define (term-δ i)
  ;; reason for add1 is explained in section 5.3 of the GCIC paper
  `(λ (x : (? ,(add1 i))) (x x)))

(define (term-Ω i)
  `(,(term-δ i) ,(term-δ i)))

(define prog-eq-nat-2
  `(,default-variant
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-nat
    ,ind-def-eq-nat
    ((λ (p : (EqNat ,term-two ,term-two)) p)
     (@ EqNat refl-nat ,term-two ,term-two & (@ Unit tt &)))))
