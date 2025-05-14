# Evaluating prog-eq-nat-2

Here is the result:
```
(@ EqNat refl-nat
  (< (Nat) <== (Nat) >
   (@ Nat succ & 
      (< (Nat) <== (Nat) > 
       (@ Nat succ & 
          (< (Nat) <== (Nat) > (@ Nat zero &))))))
  (< (Nat) <== (Nat) >
   (@ Nat succ & 
      (< (Nat) <== (Nat) >
       (@ Nat succ & (< (Nat) <== (Nat) > (@ Nat zero &))))))
  &
  (< ((elim Nat 
       (< (Nat) <== (Nat) > 
        (@ Nat succ & 
         (< (Nat) <== (Nat) > 
          (@ Nat succ & 
           (< (Nat) <== (Nat) > (@ Nat zero &))))))
       as (λ (__2396974) (Π (__2396975 : (Nat)) (□ 0)))
       rec f1_2396976 with 
       [(zero) => 
        (< (Π (__2397020 : (Nat)) (□ 0)) <== (Π (n2_2397019 : (Nat)) (□ 0)) >
         (λ (n2_2397010 : (Nat))
           (elim Nat n2_2397010 as (λ (__2397015) (□ 0)) rec __2397016 with
            [(zero) => (< (□ 0) <== (□ 0) > (Unit))]
            [(succ __2397018) => (< (□ 0) <== (□ 0) > (Void))])))]
       [(succ n1^_2397021) =>
        (< (Π (__2397043 : (Nat)) (□ 0)) <== (Π (n2_2397042 : (Nat)) (□ 0)) >
         (λ (n2_2397033 : (Nat))
           (elim Nat n2_2397033 as (λ (__2397038) (□ 0)) rec __2397039 with
            [(zero) => (< (□ 0) <== (□ 0) > (Void))]
            [(succ n2^_2397041) => 
             (< (□ 0) <== (□ 0) > 
              ((f1_2396976 (< (Nat) <== (Nat) > n1^_2397021))
               (< (Nat) <== (Nat) > n2^_2397041)))])))])
      (< (Nat) <== (Nat) > 
       (< (Nat) <== (Nat) > 
        (@ Nat succ & 
           (< (Nat) <== (Nat) > 
            (@ Nat succ & 
               (< (Nat) <== (Nat) > (@ Nat zero &))))))))
   <== ((elim Nat 
         (< (Nat) <== (Nat) >
          (@ Nat succ & 
             (< (Nat) <== (Nat) > 
              (@ Nat succ & 
               (< (Nat) <== (Nat) > (@ Nat zero &))))))
         as (λ (__2396904) (Π (__2396905 : (Nat)) (□ 0))) rec f1_2396906 with 
         [(zero) => 
          (< (Π (__2396950 : (Nat)) (□ 0)) <== (Π (n2_2396949 : (Nat)) (□ 0)) >
           (λ (n2_2396940 : (Nat))
             (elim Nat n2_2396940 as (λ (__2396945) (□ 0)) rec __2396946 with 
              [(zero) => (< (□ 0) <== (□ 0) > (Unit))]
              [(succ __2396948) => (< (□ 0) <== (□ 0) > (Void))])))]
         [(succ n1^_2396951) => 
          (< (Π (__2396973 : (Nat)) (□ 0)) <== (Π (n2_2396972 : (Nat)) (□ 0)) >
           (λ (n2_2396963 : (Nat))
             (elim Nat n2_2396963 as (λ (__2396968) (□ 0)) rec __2396969 with 
              [(zero) => (< (□ 0) <== (□ 0) > (Void))]
              [(succ n2^_2396971) =>
               (< (□ 0) <== (□ 0) > 
                ((f1_2396906 (< (Nat) <== (Nat) > n1^_2396951))
                 (< (Nat) <== (Nat) > n2^_2396971)))])))])
        (< (Nat) <== (Nat) > 
         (< (Nat) <== (Nat) > 
          (@ Nat succ &
             (< (Nat) <== (Nat) > 
              (@ Nat succ & 
                 (< (Nat) <== (Nat) > (@ Nat zero &)))))))) 
   > 
   (< ((elim Nat 
        (< (Nat) <== (Nat) > 
         (@ Nat succ & 
            (< (Nat) <== (Nat) >
             (@ Nat succ &
                (< (Nat) <== (Nat) > 
                 (@ Nat zero &))))))
        as (λ (__2391382) (Π (__2391383 : (Nat)) (□ 0))) rec f1_2391384 with
        [(zero) => 
         (< (Π (__2391428 : (Nat)) (□ 0)) <== (Π (n2_2391427 : (Nat)) (□ 0)) >
          (λ (n2_2391418 : (Nat))
            (elim Nat n2_2391418 as (λ (__2391423) (□ 0)) rec __2391424 with 
             [(zero) => (< (□ 0) <== (□ 0) > (Unit))]
             [(succ __2391426) => (< (□ 0) <== (□ 0) > (Void))])))]
        [(succ n1^_2391429) => 
         (< (Π (__2391451 : (Nat)) (□ 0)) <== (Π (n2_2391450 : (Nat)) (□ 0)) >
          (λ (n2_2391441 : (Nat))
            (elim Nat n2_2391441 as (λ (__2391446) (□ 0)) rec __2391447 with 
             [(zero) => (< (□ 0) <== (□ 0) > (Void))]
             [(succ n2^_2391449) => 
              (< (□ 0) <== (□ 0) > 
               ((f1_2391384 (< (Nat) <== (Nat) > n1^_2391429))
                (< (Nat) <== (Nat) > n2^_2391449)))])))])
       (< (Nat) <== (Nat) > 
        (< (Nat) <== (Nat) > 
         (@ Nat succ & 
            (< (Nat) <== (Nat) > 
             (@ Nat succ & 
                (< (Nat) <== (Nat) > 
                 (@ Nat zero &))))))))
    <== (Unit) 
    > 
    (@ Unit tt &))))
```

Here is the result after α-renaming and extracting common sub-expressions:
```
(define two 
  (< (Nat) <== (Nat) >
   (@ Nat succ & 
      (< (Nat) <== (Nat) > 
       (@ Nat succ & 
          (< (Nat) <== (Nat) > (@ Nat zero &)))))))
(define elim-two
  ((elim Nat 
    two
    as (λ (_) (Π (_ : (Nat)) (□ 0))) rec f1 with 
    [(zero) => 
     (< (Π (_ : (Nat)) (□ 0)) <== (Π (_ : (Nat)) (□ 0)) >
      (λ (n2 : (Nat))
        (elim Nat n2 as (λ (_) (□ 0)) rec _ with
         [(zero) => (< (□ 0) <== (□ 0) > (Unit))]
         [(succ _) => (< (□ 0) <== (□ 0) > (Void))])))]
    [(succ n1^) =>
     (< (Π (_ : (Nat)) (□ 0)) <== (Π (_ : (Nat)) (□ 0)) >
      (λ (n2 : (Nat))
        (elim Nat n2 as (λ (_) (□ 0)) rec _ with
         [(zero) => (< (□ 0) <== (□ 0) > (Void))]
         [(succ n2^) => 
          (< (□ 0) <== (□ 0) > 
           ((f1 (< (Nat) <== (Nat) > n1^))
            (< (Nat) <== (Nat) > n2^)))])))])
   (< (Nat) <== (Nat) > two)))

(@ EqNat refl-nat two two &
  (< elim-two <== elim-two > 
   (< elim-two <== (Unit) > 
    (@ Unit tt &))))
```

# ccic-Ω before and after cast optimization in CHECK elaboration rule

With cast optimization:
((λ (x : (< (□ 2) <== (? (□ 3)) > (? (? (□ 3)))))
   ((< (Π (_ : (? (□ 2))) (? (□ 2))) <== (< (□ 2) <== (? (□ 3)) > (? (? (□ 3)))) > x)
    x))
 (< (< (□ 2) <== (? (□ 3)) > (? (? (□ 3)))) 
    <== 
    (Π (x : (< (□ 2) <== (? (□ 3)) > (? (? (□ 3))))) (? (□ 2))) > 
  (λ (x : (< (□ 2) <== (? (□ 3)) > (? (? (□ 3)))))
    ((< (Π (_ : (? (□ 2))) (? (□ 2))) <== (< (□ 2) <== (? (□ 3)) > (? (? (□ 3)))) > x)
     x))))

Without cast optimization:
((λ (x : (< (□ 2) <== (? (□ 3)) > (? (? (□ 3)))))
   ((< (Π (_ : (? (□ 2))) (? (□ 2))) <== (< (□ 2) <== (? (□ 3)) > (? (? (□ 3)))) > x)
    (< (? (□ 2)) <== (< (□ 2) <== (? (□ 3)) > (? (? (□ 3)))) > x)))
 (< (< (□ 2) <== (? (□ 3)) > (? (? (□ 3))))
    <== 
    (Π (_ : (< (□ 2) <== (? (□ 3)) > (? (? (□ 3))))) (? (□ 2))) >
  (λ (x : (< (□ 2) <== (? (□ 3)) > (? (? (□ 3)))))
    ((< (Π (_ : (? (□ 2))) (? (□ 2))) <== (< (□ 2) <== (? (□ 3)) > (? (? (□ 3)))) > x)
     (< (? (□ 2)) <== (< (□ 2) <== (? (□ 3)) > (? (? (□ 3)))) > x)))))
