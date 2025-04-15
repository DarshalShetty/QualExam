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

(define ind-def-vec-f
  '(data VecF (A : (□ 0)) (n : (Nat))
         ((nil-f (_ : (EqNat (encode-nat 0) n)))
          (cons-f (_ : A)
                  (m : (Nat))
                  (_ : (EqNat (@ Nat succ & m) n))
                  (_ : (VecF A m))))))

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

(define fun-add
  '(λ (m : (Nat))
     (λ (n : (Nat))
       (elim Nat n as (λ (_) (Nat)) rec succ-app with
             [(zero) => m]
             [(succ n) => (@ Nat succ & (succ-app n))]))))

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
