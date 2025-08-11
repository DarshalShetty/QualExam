#lang racket

(provide (all-defined-out))

(define default-variant
  '(variant gcic-n))

(define (let-bind var rhs-type rhs body)
  `((λ (,var : ,rhs-type)
     ,body)
    ,rhs))

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
       (elim Nat m as (λ (_) (Nat)) rec succ-app with
             [(zero) => n]
             [(succ m) => (@ Nat succ & (succ-app m))]))))

(define fun-leb
  '(λ (m : (Nat))
     (elim Nat m as (λ (_) (Π (n : (Nat)) (Bool))) rec F with
           [(zero) => (λ (n : (Nat))
                        (@ Bool true &))]
           [(succ m) => (λ (n : (Nat))
                          (elim Nat n as (λ (_) (Bool)) rec _ with
                                [(zero) => (@ Bool false &)]
                                [(succ n) => ((F m) n)]))])))

(define ind-def-unit
  '(data Unit
         ((tt))))

(define ind-def-void
  '(data Void
         ()))

(define fun-eq-nat?
  '(λ (m : (Nat))
     (λ (n : (Nat))
       ((elim Nat m as (λ (_) (Π (_ : (Nat)) (□ 0))) rec f1 with
              [(zero) => (λ (n : (Nat))
                           (elim Nat n as (λ (_) (□ 0)) rec _ with
                                 [(zero) => (Unit)]
                                 [(succ _) => (Void)]))]
              [(succ m^)
               =>
               (λ (n : (Nat))
                 (elim Nat n as (λ (_) (□ 0)) rec _ with
                       [(zero) => (Void)]
                       [(succ n^) => ((f1 m^) n^)]))])
        n))))

(define ind-def-eq-nat
  `(data EqNat (n1 : (Nat)) (n2 : (Nat))
         ((refl-nat (_ : ((,fun-eq-nat? n1) n2))))))

(define proof-inj-eq-nat
  `(λ (m : (Nat))
     (λ (n : (Nat))
       (λ (H : (EqNat m n))
         (@ EqNat refl-nat (@ Nat succ & m) (@ Nat succ & n) &
            (elim EqNat H as (λ (_) ((,fun-eq-nat? m) n))
                  rec _ with
                  ((refl-nat e) => e)))))))

(define prog-inj-eq-nat
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,proof-inj-eq-nat))

(define proof-proj-eq-nat
  `(λ (m : (Nat))
     (λ (n : (Nat))
       (λ (H : (EqNat (@ Nat succ & m) (@ Nat succ & n)))
         (@ EqNat refl-nat m n &
            (elim EqNat H as (λ (_) ((,fun-eq-nat? m) n))
                  rec _ with
                  ((refl-nat e) => e)))))))

(define prog-proj-eq-nat
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,proof-proj-eq-nat))

(define proof-false-O-S
  `(λ (n : (Nat))
     (λ (H : (EqNat ,(encode-nat 0) (@ Nat succ & n)))
       (elim EqNat H as (λ (_) (Void)) rec _ with
             ((refl-nat e) => e)))))

(define prog-false-O-S
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,proof-false-O-S))

(define proof-sym-eq-nat
  `(λ (m : (Nat))
     (elim Nat m as (λ (m0) (Π (n : (Nat)) (Π (_ : (EqNat m0 n)) (EqNat n m0))))
           rec F with
           ((zero)
            =>
            (λ (n : (Nat))
              (elim Nat n as (λ (n0) (Π (_ : (EqNat ,(encode-nat 0) n0)) (EqNat n0 ,(encode-nat 0))))
                    rec _ with
                    ((zero) => (λ (X : (EqNat ,(encode-nat 0) ,(encode-nat 0))) X))
                    ((succ n0)
                     =>
                     (λ (X : (EqNat ,(encode-nat 0) (@ Nat succ & n0)))
                       (elim Void ((,proof-false-O-S n0) X) as
                             (λ (_) (EqNat (@ Nat succ & n0) ,(encode-nat 0)))
                             rec _ with))))))
           ((succ m0)
            =>
            (λ (n : (Nat))
              (elim Nat n as
                    (λ (n0) (Π (_ : (EqNat (@ Nat succ & m0) n0))
                               (EqNat n0 (@ Nat succ & m0))))
                    rec _ with
                    ((zero)
                     =>
                     (λ (X : (EqNat (@ Nat succ & m0) ,(encode-nat 0)))
                       (elim EqNat X as
                             (λ (_) (EqNat ,(encode-nat 0) (@ Nat succ & m0)))
                             rec _ with
                             ((refl-nat e)
                              =>
                              (elim Void e as
                                    (λ (_) (EqNat ,(encode-nat 0) (@ Nat succ & m0)))
                                    rec _ with)))))
                    ((succ n0)
                     =>
                     (λ (X : (EqNat (@ Nat succ & m0) (@ Nat succ & n0)))
                       (((,proof-inj-eq-nat n0) m0)
                        (((F m0) n0) (((,proof-proj-eq-nat m0) n0) X)))))))))))

(define prog-sym-eq-nat
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,proof-sym-eq-nat))

(define (proof-refl-eq-nat inj-eq-nat)
  `(λ (n : (Nat))
     (elim Nat n as (λ (n^) (EqNat n^ n^)) rec refl-n-n with
           [(zero) => (@ EqNat refl-nat ,(encode-nat 0) ,(encode-nat 0) & (@ Unit tt &))]
           [(succ n^)
            =>
            (((,inj-eq-nat n^) n^) (refl-n-n n^))])))

(define prog-refl-eq-nat
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,(let-bind 'inj-eq-nat '(Π (m : (Nat))
                              (Π (n : (Nat))
                                 (Π (p : (EqNat m n))
                                    (EqNat (@ Nat succ & m) (@ Nat succ & n)))))
               proof-inj-eq-nat
               (proof-refl-eq-nat 'inj-eq-nat))))

(define proof-trans-eq-nat
  `(λ (m : (Nat))
     (elim Nat m as (λ (m0) (Π (n : (Nat))
                               (Π (o : (Nat))
                                  (Π (_ : (EqNat m0 n))
                                     (Π (_ : (EqNat n o))
                                        (EqNat m0 o))))))
           rec F with
           [(zero)
            =>
            (λ (n : (Nat))
              (elim Nat n as (λ (n0)
                               (Π (o : (Nat))
                                  (Π (_ : (EqNat ,(encode-nat 0) n0))
                                     (Π (_ : (EqNat n0 o))
                                        (EqNat ,(encode-nat 0) o)))))
                    rec _ with
                    ((zero)
                     =>
                     (λ (o : (Nat))
                       (λ (_ : (EqNat ,(encode-nat 0) ,(encode-nat 0)))
                         (λ (H : (EqNat ,(encode-nat 0) o))
                           H))))
                     ((succ n0)
                      =>
                      (λ (o : (Nat))
                        (λ (H : (EqNat ,(encode-nat 0) (@ Nat succ & n0)))
                          (λ (_ : (EqNat (@ Nat succ & n0) o))
                           (elim Void ((,proof-false-O-S n0) H)
                                 as (λ (_) (EqNat ,(encode-nat 0) o))
                                 rec _ with)))))))]
           [(succ m0)
            =>
            (λ (n : (Nat))
              (elim Nat n as (λ (n0) (Π (o : (Nat))
                                        (Π (_ : (EqNat (@ Nat succ & m0) n0))
                                           (Π (_ : (EqNat n0 o))
                                              (EqNat (@ Nat succ & m0) o)))))
                    rec _ with
                    ((zero)
                     =>
                     (λ (o : (Nat))
                       (λ (H : (EqNat (@ Nat succ & m0) ,(encode-nat 0)))
                         (λ (_ : (EqNat ,(encode-nat 0) o))
                           (elim Void ((,proof-false-O-S m0)
                                       (((,proof-sym-eq-nat (@ Nat succ & m0))
                                         ,(encode-nat 0)) H))
                             as (λ (_) (EqNat (@ Nat succ & m0) o))
                             rec _ with)))))
                ((succ n0)
                 =>
                 (λ (o : (Nat))
                   (λ (H : (EqNat (@ Nat succ & m0) (@ Nat succ & n0)))
                     (λ (H0 : (EqNat (@ Nat succ & n0) o))
                      ((elim Nat o as
                            (λ (n2)
                              (Π (_ : (EqNat (@ Nat succ & n0) n2))
                                 (EqNat (@ Nat succ & m0) n2)))
                            rec _ with
                            ((zero)
                             =>
                             (λ (X0 : (EqNat (@ Nat succ & n0) ,(encode-nat 0)))
                               (elim Void ((,proof-false-O-S n0)
                                           (((,proof-sym-eq-nat (@ Nat succ & n0))
                                             ,(encode-nat 0)) X0))
                                     as (λ (_) (EqNat (@ Nat succ & m0) ,(encode-nat 0)))
                                     rec _ with)))
                            ((succ n2)
                             =>
                             (λ (X0 : (EqNat (@ Nat succ & n0) (@ Nat succ & n2)))
                               (((,proof-inj-eq-nat m0) n2)
                                (((((F m0) n0) n2) (((,proof-proj-eq-nat m0) n0) H))
                                 (((,proof-proj-eq-nat n0) n2) X0))))))
                       H0)))))))])))

(define prog-trans-eq-nat
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,proof-trans-eq-nat))

(define (proof-n=0+n refl-eq-nat)
  `(λ (m : (Nat))
     (λ (n : (Nat))
       (elim Nat m as (λ (m^) (Π (_ : (EqNat ,(encode-nat 0) m^))
                                 (EqNat n ((,fun-add m^) n))))
             rec _ with
             [(zero) => (λ (_ : (EqNat ,(encode-nat 0) ,(encode-nat 0)))
                           (,refl-eq-nat n))]
             [(succ m^)
              =>
              (λ (p : (EqNat ,(encode-nat 0) (@ Nat succ & m^)))
                (elim EqNat p as (λ (_) (EqNat n ((,fun-add (@ Nat succ & m^)) n)))
                      rec _ with
                      [(refl-nat contr)
                       =>
                       (elim Void contr as
                             (λ (_)
                               (EqNat n ((,fun-add (@ Nat succ & m^)) n)))
                             rec _ with
                             )]))]))))

(define prog-n=0+n
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,(let-bind 'inj-eq-nat '(Π (m : (Nat))
                               (Π (n : (Nat))
                                  (Π (p : (EqNat m n))
                                     (EqNat (@ Nat succ & m) (@ Nat succ & n)))))
               proof-inj-eq-nat
               (let-bind 'refl-eq-nat '(Π (n : (Nat)) (EqNat n n))
                         (proof-refl-eq-nat 'inj-eq-nat)
                         (proof-n=0+n 'refl-eq-nat)))))

(define ind-def-bool
  '(data Bool
         ((true)
          (false))))

(define prog-one-zero?
  `(,default-variant
    ,ind-def-nat
    ,ind-def-bool
    (elim Nat ,(encode-nat 1) as (λ (_) (Bool)) rec _ with
          [(zero) => (@ Bool true &)]
          [(succ _) => (@ Bool false &)])))

(define prog-one-zero?-unk
  `(,default-variant
    ,ind-def-nat
    ,ind-def-bool
    (elim Nat ,(encode-nat 1) as (λ (_) (? 1)) rec _ with
          [(zero) => (@ Bool true &)]
          [(succ _) => (@ Bool false &)])))

(define ind-def-list
  `(data List (A : (□ 0))
         ([null]
          [cons (_ : A) (_ : (List A))])))

(define ind-def-list-1
  `(data List1 (A : (□ 1))
         ([null]
          [cons (_ : A) (_ : (List1 1 A))])))

(define ind-def-list-1-weird
  `(data List1^ (A : (□ 1))
         ([null]
          [cons (_ : A) (_ : (List1^ 0 A))])))

(define (encode-list-nat ls)
  (for/foldr ([res '(@ List null (Nat) &)])
             ([l ls])
    `(@ List cons (Nat) & ,(encode-nat l) ,res)))

(define prog-nat-one
  `(,default-variant
    ,ind-def-nat
    ,(encode-nat 1)))

(define prog-norm-in-elab
  `(,default-variant
    ,ind-def-nat
    ((λ (x : ((λ (t : (□ 0)) t) (Nat))) x) ,(encode-nat 0))))

(define prog-list-nat-one
  `(,default-variant
    ,ind-def-nat
    ,ind-def-list
    (@ List cons (Nat) & ,(encode-nat 1)
       (@ List null (Nat) &))))

(define prog-list-univ-err
  `(,default-variant
    ,ind-def-nat
    ,ind-def-list
    (@ List cons (□ 0) & (Nat)
       (@ List null (□ 0) &))))

(define prog-list-univ
  `(,default-variant
    ,ind-def-nat
    ,ind-def-list-1
    (@ List1 cons 1 (□ 0) & (Nat)
       (@ List1 null 1 (□ 0) &))))

(define prog-list-univ-weird
  `(,default-variant
    ,ind-def-nat
    ,ind-def-list-1-weird
    (@ List1^ cons (□ 0) & (Nat)
       (@ List1^ null (□ 0) &))))

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

(define fun-length
  `(λ (A : (□ 0))
     (λ (l : (List A))
       (elim List l as (λ (_) (Nat)) rec F with
               [(null) => ,(encode-nat 0)]
               [(cons hd tl) => (@ Nat succ & (F tl))]))))

(define prog-list-length-123
  `(,default-variant
    ,ind-def-nat
    ,ind-def-list
    ((,fun-length (Nat))
      ,(encode-list-nat '(1 2 3)))))

(define ind-def-vec-f
  `(data VecF (A : (□ 0)) (n : (Nat))
         ((nil-f (_ : (EqNat ,(encode-nat 0) n)))
          (cons-f (_ : A)
                  (m : (Nat))
                  (_ : (EqNat (@ Nat succ & m) n))
                  (_ : (VecF A m))))))

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


(define fun-head-f
  `(λ (A : (□ 0))
     (λ (n : (Nat))
       (λ (v : (VecF A (@ Nat succ & n)))
         (elim VecF v as (λ (_) A) rec _ with
               [(nil-f eq-0-Sn)
                =>
                (elim EqNat eq-0-Sn as (λ (_) A) rec _ with
                      [(refl-nat contr)
                       =>
                       (elim Void contr as (λ (_) A) rec _ with)])]
               [(cons-f hd _ _ _) => hd])))))

(define prog-head-f
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,ind-def-vec-f
    (((,fun-head-f (Nat)) ,(encode-nat 2))
     ,(encode-vec-f-nat '(42 43 44)))))

#|
      (fix F (n :nat) : forall (v : VecF A n), VecF A (filter_len A n f v) :=
         match n as n0 return forall (v : VecF A n0), VecF A (filter_len A n0 f v) with
         | O => fun (v : VecF A 0) =>
                 match v as v0 return VecF A (filter_len A 0 f v0) with
                 | nil_f _ _ e => nil_f _ _ e
                 | cons_f _ _ y m e v0 =>
                     match e with
                     | refl_nat _ _ contr =>
                         match contr return VecF A (filter_len A 0 f (cons_f A 0 y m e v0)) with end
                     end
                 end
         | S n0 => fun (v : VecF A (S n0)) =>
                    match v as v0 return VecF A (filter_len A (S n0) f v0) with
                    | nil_f _ _ e =>
                        match e with
                        | refl_nat _ _ contr =>
                            match contr return VecF A (filter_len A (S n0) f (nil_f A (S n0) e)) with end
                        end

                    | cons_f _ _ hd m e v0 => _
                    end
         end
|#

(define fun-filter-f
  `(λ (A : (□ 0))
     (λ (n : (Nat))
       (λ (f : (Π (a : A) (Bool)))
         (elim Nat n as (λ (n^) (Π (v : (VecF A n^)) (VecF A (? 0)))) rec F with
                 [(zero)
                  =>
                  (λ (v : (VecF A ,(encode-nat 0))) v)]
                 [(succ n^)
                  =>
                  (λ (v : (VecF A (@ Nat succ & n^)))
                    (elim VecF v as (λ (_) (VecF A (? 0))) rec _ with
                          [(nil-f eq-0-Sn^)
                           =>
                           (elim EqNat eq-0-Sn^ as
                                 (λ (_)
                                   (VecF A (? 0)))
                                 rec _ with
                                 [(refl-nat contr)
                                  =>
                                  (elim Void contr as
                                        (λ (_)
                                          (VecF A (? 0)))
                                        rec _ with)])]
                          [(cons-f hd m _ tl-m)
                           =>
                           (elim Bool (f hd) as
                                 (λ (_)
                                   (VecF A (? 0)))
                                 rec _ with
                                 [(true)
                                  =>
                                  (@ VecF cons-f A (@ Nat succ & (? 0))
                                     &
                                     hd (? 0) (? 0) ((F m) tl-m))]
                                 [(false)
                                  =>
                                  ((F m) tl-m)])]))])))))

(define prog-vec-f-filter-leb4-35
  `(,default-variant
    ,ind-def-nat
    ,ind-def-bool
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,ind-def-vec-f
    ((((,fun-filter-f (Nat))
        ,(encode-nat 2))
      (λ (n : (Nat)) ((,fun-leb n) ,(encode-nat 4))))
     ,(encode-vec-f-nat '(3 5)))))


(define prog-example-1
  `(,default-variant
    ,ind-def-nat
    ,ind-def-bool
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,ind-def-vec-f
    (((,fun-head-f (Nat)) (? 0))
     ((((,fun-filter-f (Nat))
        ,(encode-nat 2))
       (λ (n : (Nat)) ((,fun-leb n) ,(encode-nat 4))))
      ,(encode-vec-f-nat '(3 5))))))

(define prog-example-1-err
  `(,default-variant
    ,ind-def-nat
    ,ind-def-bool
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,ind-def-vec-f
    (((,fun-head-f (Nat)) (? 0))
     ((((,fun-filter-f (Nat))
        ,(encode-nat 2))
       (λ (n : (Nat)) ((,fun-leb n) ,(encode-nat 4))))
      ,(encode-vec-f-nat '(7 5))))))

(define fun-compose
  '(λ (A : (□ 0))
     (λ (B : (□ 0))
       (λ (C : (□ 0))
         (λ (f : (Π (_ : B) C))
           (λ (g : (Π (_ : A) B))
            (λ (x : A)
              (f (g x)))))))))

(define prog-compose-≤3-length-123
  `(,default-variant
    ,ind-def-bool
    ,ind-def-nat
    ,ind-def-list
    ((((((,fun-compose (List (Nat))) (Nat)) (Bool))
      (λ (n : (Nat)) ((,fun-leb n) ,(encode-nat 3))))
     (,fun-length (Nat)))
     ,(encode-list-nat '(1 2 3)))))

(define proof-subst-vec-f
  `(λ (m : (Nat))
     (elim Nat m as (λ (m^)
                      (Π (n : (Nat))
                         (Π (A : (□ 0))
                            (Π (p : (EqNat m^ n))
                               (Π (v : (VecF A m^))
                                  (VecF A n))))))
           rec subst-rec with
           [(zero)
            =>
            (λ (n : (Nat))
              (elim Nat n as (λ (n^)
                               (Π (A : (□ 0))
                                  (Π (p : (EqNat ,(encode-nat 0) n^))
                                     (Π (v : (VecF A ,(encode-nat 0)))
                                        (VecF A n^)))))
                    rec _ with
                    [(zero)
                     =>
                     (λ (A : (□ 0))
                       (λ (p : (EqNat ,(encode-nat 0) ,(encode-nat 0)))
                         (λ (v : (VecF A ,(encode-nat 0)))
                           v)))]
                    [(succ n^)
                     =>
                     (λ (A : (□ 0))
                       (λ (p : (EqNat ,(encode-nat 0) (@ Nat succ & n^)))
                         (λ (v : (VecF A ,(encode-nat 0)))
                           (elim EqNat p as
                                 (λ (_)
                                   (VecF A (@ Nat succ & n^)))
                                 rec _ with
                                 [(refl-nat contr)
                                  =>
                                  (elim Void contr as
                                        (λ (_)
                                          (VecF A (@ Nat succ & n^)))
                                        rec _ with)]))))]))]
           [(succ m^)
            =>
            (λ (n : (Nat))
              (elim Nat n as (λ (n^)
                               (Π (A : (□ 0))
                                  (Π (p : (EqNat (@ Nat succ & m^) n^))
                                     (Π (v : (VecF A (@ Nat succ & m^)))
                                        (VecF A n^)))))
                    rec _ with
                    [(zero)
                     =>
                     (λ (A : (□ 0))
                       (λ (p : (EqNat (@ Nat succ & m^) ,(encode-nat 0)))
                         (λ (v : (VecF A (@ Nat succ & m^)))
                           (elim EqNat p as
                                 (λ (_)
                                   (VecF A ,(encode-nat 0)))
                                 rec _ with
                                 [(refl-nat contr)
                                  =>
                                  (elim Void contr as
                                        (λ (_)
                                          (VecF A ,(encode-nat 0)))
                                        rec _ with)]))))]
                    [(succ n^)
                     =>
                     (λ (A : (□ 0))
                       (λ (eq-Sm^-Sn^ : (EqNat (@ Nat succ & m^) (@ Nat succ & n^)))
                         (λ (v : (VecF A (@ Nat succ & m^)))
                           (elim VecF v as
                                 (λ (_)
                                   (VecF A (@ Nat succ & n^)))
                                 rec _ with
                                 [(nil-f eq-0-Sm^)
                                  =>
                                  (elim EqNat eq-0-Sm^ as
                                        (λ (_)
                                          (VecF A (@ Nat succ & n^)))
                                        rec _ with
                                        [(refl-nat contr)
                                         =>
                                         (elim Void contr as
                                               (λ (_)
                                                 (VecF A (@ Nat succ & n^)))
                                               rec _ with)])]
                                 [(cons-f hd m^^ eq-Sm^^-Sm^ tl-m^^)
                                  =>
                                  (elim EqNat eq-Sm^-Sn^ as
                                        (λ (_)
                                          (VecF A (@ Nat succ & n^)))
                                        rec _ with
                                        [(refl-nat m^=n^?)
                                         =>
                                         (elim EqNat eq-Sm^^-Sm^ as
                                               (λ (_)
                                                 (VecF A (@ Nat succ & n^)))
                                               rec _ with
                                               [(refl-nat m^^=m^?)
                                                =>
                                                (@ VecF
                                                   cons-f
                                                   A
                                                   (@ Nat succ & n^)
                                                   &
                                                   hd
                                                   m^
                                                   (@ EqNat
                                                      refl-nat
                                                      (@ Nat succ & m^)
                                                      (@ Nat succ & n^)
                                                      &
                                                      m^=n^?)
                                                   (((((subst-rec
                                                        m^^) m^)
                                                      A)
                                                     (@ EqNat
                                                        refl-nat
                                                        m^^
                                                        m^
                                                        &
                                                        m^^=m^?))
                                                    tl-m^^))])])]))))]))])))

(define prog-subst-vec-f
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,ind-def-vec-f
    ,proof-subst-vec-f))

#;
(define fun-vec-f-append
  `(λ (A : (□ 0))
     (λ (m : (Nat))
       (λ (n : (Nat))
         (λ (v1 : (VecF A m))
           (λ (v2 : (VecF A n))
             (elim VecF v1 as (λ (_) (VecF A ((,fun-add m) n))) rec append-v2 with
                   [(nil-f eq-0-m)
                    =>
                    (((((,proof-subst-vec-f n) ((,fun-add m) n)) A)
                      (((,(proof-n=0+n (proof-refl-eq-nat proof-inj-eq-nat)) m) n)
                       eq-0-m))
                     v2)]
                   [(cons-f hd m^ eq-Sm^-m tl) =>
                    (@ VecF cons-f A (? 0) & hd (? 0) (? 0) (append-v2 tl))])))))))

(define fun-vec-f-append
  `(λ (A : (□ 0))
     (λ (m : (Nat))
       (λ (n : (Nat))
         (λ (v1 : (VecF A m))
           (λ (v2 : (VecF A n))
             ((elim Nat m as
                    (λ (m1) (Π (_ : (VecF A m1)) (VecF A ((,fun-add m1) n))))
                    rec F with
                    [(zero) => (λ (_ : (VecF A (@ Nat zero &))) v2)]
                    [(succ m1)
                     =>
                     (λ (v3 : (VecF A (@ Nat succ & m1)))
                       (elim VecF v3 as (λ (_) (VecF A ((,fun-add (@ Nat succ & m1)) n))) rec _ with
                             [(nil-f eq-0-Sm1)
                              =>
                              (elim EqNat eq-0-Sm1 as
                                    (λ (_)
                                      (VecF A ((,fun-add (@ Nat succ & m1)) n)))
                                    rec _ with
                                    [(refl-nat contr)
                                     =>
                                     (elim Void contr as
                                           (λ (_)
                                             (VecF A ((,fun-add (@ Nat succ & m1)) n)))
                                           rec _ with)])]
                             [(cons-f hd m2 eq-Sm2-Sm1 v-tl)
                              =>
                              (@ VecF cons-f A ((,fun-add (@ Nat succ & m1)) n) &
                                 hd ((,fun-add m1) n)
                                 (,(proof-refl-eq-nat proof-inj-eq-nat) ((,fun-add (@ Nat succ & m1)) n))
                                 ((F m1)
                                  (((((,proof-subst-vec-f m2) m1) A)
                                    (elim EqNat eq-Sm2-Sm1 as (λ (_) (EqNat m2 m1)) rec _ with
                                          [(refl-nat m2=m1?)
                                           =>
                                           (@ EqNat refl-nat m2 m1 & m2=m1?)]))
                                   v-tl)))]))])
              v1)))))))

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

(define prog-vec-f-append-1-0
  `(,default-variant
    ,ind-def-nat
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-eq-nat
    ,ind-def-vec-f
    (((((,fun-vec-f-append (Nat))
        ,(encode-nat 0))
       ,(encode-nat 1))
      ,(encode-vec-f-nat '()))
     ,(encode-vec-f-nat '(0)))))

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

(define (fun-vec-μ-append Vecμ)
  `(λ (A : (□ 0))
     (λ (m : (Nat))
       (elim Nat m as (λ (m^)
                        (Π (n : (Nat))
                           (Π (_ : ((,Vecμ A) m^))
                              (Π (_ : ((,Vecμ A) n))
                                 ((,Vecμ A) ((,fun-add m^) n))))))
             rec append-m with
             [(zero) => (λ (n : (Nat))
                          (λ (v1 : ((,Vecμ A) (@ Nat zero &)))
                            (λ (v2 : ((,Vecμ A) n))
                              v2)))]
             [(succ m^)
              =>
              (λ (n : (Nat))
                (λ (v1 : ((,Vecμ A) (@ Nat succ & m^)))
                  (λ (v2 : ((,Vecμ A) n))
                    (elim Prod v1 as (λ (_) ((,Vecμ A)
                                             (@ Nat succ & ((,fun-add m^) n))))
                          rec _ with
                          [(pair hd tl) => (@ Prod pair A ((,Vecμ A) ((,fun-add m^) n)) &
                                              hd ((((append-m m^) n) tl) v2))]))))]))))

(define prog-vec-μ-append-12-34
  `(,default-variant
    ,ind-def-nat
    ,ind-def-prod
    ,ind-def-unit
    (((((,(fun-vec-μ-append fun-vec-μ) (Nat))
        ,(encode-nat 2))
       ,(encode-nat 2))
      ,(encode-vec-μ-nat '(1 2)))
     ,(encode-vec-μ-nat '(3 4)))))

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

(define prog-leb-2-3
  `(,default-variant
    ,ind-def-nat
    ,ind-def-bool
    ((,fun-leb ,term-two) ,term-three)))

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

(define prog-blame
  `(,default-variant
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-bool
    ,ind-def-nat
    ,ind-def-eq-nat
    ,ind-def-vec-f
    ((((((,fun-compose (VecF (Nat) ,(encode-nat 3))) (VecF (Nat) (? 0))) (Nat))
       ((,fun-head-f (Nat)) (? 0)))
      (((,fun-filter-f (Nat)) ,(encode-nat 3))
       (λ (n : (Nat)) ((,fun-leb n) ,(encode-nat 4)))))
     ,(encode-vec-f-nat '(11 12 13)))))

(define ind-def-fin-f
  '(data FinF (n : (Nat))
         ((fzero (m : (Nat)) (_ : (EqNat (@ Nat succ & m) n)))
          (fsucc (m : (Nat)) (_ : (FinF m)) (_ : (EqNat (@ Nat succ & m) n))))))

(define (encode-fin N n)
  (define init-pre (encode-nat (sub1 (- N n))))
  (define succ-pre `(@ Nat succ & ,init-pre))
  (for/fold ([res `(@ FinF fzero ,succ-pre
                      & ,init-pre
                      (@ EqNat refl-nat ,succ-pre ,succ-pre
                         & (@ Unit tt &)))]
             [pre succ-pre]
             #:result res)
            ([_ (in-range n)])
    (define next-pre `(@ Nat succ & ,pre))
    (values
     `(@ FinF fsucc ,next-pre & ,pre ,res
             (@ EqNat refl-nat ,next-pre ,next-pre
                      & (@ Unit tt &)))
     next-pre)))

(define prog-fin-3
  `(,default-variant
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-nat
    ,ind-def-eq-nat
    ,ind-def-fin-f
    ((λ (x : (FinF ,(encode-nat 5))) x) ,(encode-fin 5 3))))

(define prog-fin-3-typefail
  `(,default-variant
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-nat
    ,ind-def-eq-nat
    ,ind-def-fin-f
    ((λ (x : (FinF ,(encode-nat 2))) x) ,(encode-fin 2 3))))

(define proof-false-fin-O
  `(λ (n : (FinF ,(encode-nat 0)))
     (elim FinF n as (λ (_) (Void))
           rec _ with
           ((fzero m e)
            =>
            ((,proof-false-O-S m)
             (((,proof-sym-eq-nat (@ Nat succ & m)) ,(encode-nat 0)) e)))
           ((fsucc m f e)
            =>
            ((,proof-false-O-S m)
             (((,proof-sym-eq-nat (@ Nat succ & m)) ,(encode-nat 0)) e))))))

(define prog-false-fin-O
  `(,default-variant
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-nat
    ,ind-def-eq-nat
    ,ind-def-fin-f
    ,proof-false-fin-O))

(define proof-subst-fin-f
  `(λ (m : (Nat))
     (elim Nat m as
           (λ (m0)
              (Π (n : (Nat))
                 (Π (_ : (EqNat m0 n))
                    (Π (_ : (FinF m0))
                       (FinF n)))))
           rec F with
           ((zero)
            =>
            (λ (n : (Nat))
              (elim Nat n as
                    (λ (n0)
                      (Π (_ : (EqNat ,(encode-nat 0) n0))
                         (Π (_ : (FinF ,(encode-nat 0)))
                            (FinF n0))))
                    rec _ with
                    ((zero)
                     =>
                     (λ (_ : (EqNat ,(encode-nat 0) ,(encode-nat 0)))
                       (λ (H : (FinF ,(encode-nat 0)))
                         H)))
                    ((succ n0)
                     =>
                     (λ (H : (EqNat ,(encode-nat 0) (@ Nat succ & n0)))
                       (λ (_ : (FinF ,(encode-nat 0)))
                         (elim Void ((,proof-false-O-S n0) H) as
                               (λ (_) (FinF (@ Nat succ & n0)))
                               rec _ with)))))))
           ((succ m0)
            =>
            (λ (n : (Nat))
              (elim Nat n as
                    (λ (n0)
                      (Π (_ : (EqNat (@ Nat succ & m0) n0))
                         (Π (_ : (FinF (@ Nat succ & m0)))
                            (FinF n0))))
                    rec _ with
                    ((zero)
                     =>
                     (λ (H : (EqNat (@ Nat succ & m0) ,(encode-nat 0)))
                       (λ (_ : (FinF (@ Nat succ & m0)))
                         (elim Void ((,proof-false-O-S m0)
                                     (((,proof-sym-eq-nat (@ Nat succ & m0))
                                       ,(encode-nat 0)) H))
                               as (λ (_) (FinF ,(encode-nat 0)))
                               rec _ with))))
                    ((succ n0)
                     =>
                     (λ (H : (EqNat (@ Nat succ & m0) (@ Nat succ & n0)))
                       (λ (H0 : (FinF (@ Nat succ & m0)))
                         (elim FinF H0
                               as (λ (_) (FinF (@ Nat succ & n0)))
                               rec _ with
                               ((fzero m1 e)
                                =>
                                (@ FinF fzero (@ Nat succ & n0) &
                                   n0 (,(proof-refl-eq-nat proof-inj-eq-nat)
                                       (@ Nat succ & n0))))
                               ((fsucc m1 f e)
                                =>
                                (@ FinF fsucc (@ Nat succ & n0) &
                                   m1 f
                                   (((((,proof-trans-eq-nat (@ Nat succ & m1))
                                       (@ Nat succ & m0))
                                      (@ Nat succ & n0))
                                     e)
                                    H)))))))))))))

(define prog-subst-fin-f
  `(,default-variant
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-nat
    ,ind-def-eq-nat
    ,ind-def-fin-f
    ,proof-subst-fin-f))

(define fun-nth-f
  `(λ (A : (□ 0))
     (λ (n : (Nat))
       (elim Nat n as
             (λ (n0) (Π (_ : (VecF A n0))
                         (Π (_ : (FinF n0))
                            A)))
             rec F with
             ((zero)
              =>
              (λ (v : (VecF A ,(encode-nat 0)))
                (λ (i : (FinF ,(encode-nat 0)))
                  (elim Void (,proof-false-fin-O i) as (λ (_) A) rec _ with))))
             ((succ n^)
              =>
              (λ (v : (VecF A (@ Nat succ & n^)))
                (elim VecF v as (λ (_) (Π (_ : (FinF (@ Nat succ & n^))) A)) rec _ with
                      ((nil-f e)
                       =>
                       (λ (_ : (FinF (@ Nat succ & n^)))
                         (elim Void ((,proof-false-O-S n^) e) as (λ (_) A) rec _ with)))
                      ((cons-f hd m e v0)
                       =>
                       (λ (i : (FinF (@ Nat succ & n^)))
                         ((elim FinF i as (λ (_) (Π (_ : (VecF A n^)) A)) rec _ with
                               ((fzero _ _)
                                =>
                                (λ (_ : (VecF A n^)) hd))
                               ((fsucc o p e^)
                                =>
                                (λ (v^ : (VecF A n^))
                                  (((F n^) v^)
                                   ((((,proof-subst-fin-f o) n^)
                                     (((,proof-proj-eq-nat o) n^) e^))
                                    p)))))
                          (((((,proof-subst-vec-f m) n^) A)
                            (((,proof-proj-eq-nat m) n^) e))
                           v0)))))))))))

(define prog-nth-1-34
  `(,default-variant
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-nat
    ,ind-def-eq-nat
    ,ind-def-vec-f
    ,ind-def-fin-f
    ((((,fun-nth-f (Nat)) ,(encode-nat 2)) ,(encode-vec-f-nat '(3 4)))
     ,(encode-fin 2 1))))

(define prog-nth-3-1234
  `(,default-variant
    ,ind-def-unit
    ,ind-def-void
    ,ind-def-nat
    ,ind-def-eq-nat
    ,ind-def-vec-f
    ,ind-def-fin-f
    ((((,fun-nth-f (Nat)) ,(encode-nat 4)) ,(encode-vec-f-nat '(1 2 3 4)))
     ,(encode-fin 4 3))))
