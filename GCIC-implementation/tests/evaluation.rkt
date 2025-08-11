#lang racket

(require rackunit)
(require "../syntax.rkt")
(require "../examples.rkt")
(require "../evaluation.rkt")
(require (except-in "../elaboration.rkt" check))

(provide ccic-Ω)

(define test-defs (parse-defs `(,ind-def-void
                                ,ind-def-unit
                                ,ind-def-bool
                                ,ind-def-nat
                                ,ind-def-eq-nat
                                ,ind-def-list)))

(check-equal? (head (parse-term `(Π (_ : (Unit)) (Void)) test-defs)) (HeadPi))

(check-equal? (head (parse-term `(List (Unit)) test-defs)) (HeadIndT 'List))

(check-equal? (head (parse-term `(□ 0) test-defs)) (HeadUniv 0))

(check-exn exn:fail? (λ () (head (parse-term `(λ (_ : (Unit)) (? (□ 0))) test-defs))))

(check-equal? (germ (HeadIndT 'List) 0 test-defs) (IndT 'List 0 (list (Unk (Univ 0)))))

;; 2 + 2 = 4
(let* ([defs (parse-defs `(,ind-def-nat))]
       [add (parse-term fun-add defs)]
       [two (parse-term term-two defs)]
       [t0 (reduce-if-principal defs (App add two))]
       [t1 (reduce-if-principal defs (App t0 two))]
       [t2 (reduce-if-principal defs t1)]
       [t3 (struct-copy Constr t2
                        [args (map reduce-if-principal defs (Constr-args t2))])]
       [t4 (struct-copy Constr t3
                        [args (map reduce-if-principal defs (Constr-args t3))])]
       [t5 (struct-copy Constr t4
                        (args (map
                               (λ (a)
                                 (let ([t5^ a])
                                   (struct-copy Constr t5^
                                                (args (map reduce-if-principal
                                                           defs
                                                           (Constr-args t5^))))))
                               (Constr-args t4))))]
       [t6 (struct-copy Constr t5
                        (args (map
                               (λ (a)
                                 (let ([t6^ a])
                                   (struct-copy Constr t6^
                                                (args (map reduce-if-principal
                                                           defs
                                                           (Constr-args t6^))))))
                               (Constr-args t5))))])
  (check-equal? t6 (parse-term (encode-nat 4) defs)))

;; less painful 2+2=4
(let* ([defs (parse-defs `(,ind-def-nat))]
       [add (parse-term fun-add defs)]
       [two (parse-term term-two defs)]
       [suc2+2 (evaluate (App (App add two) two) defs)]
       [suc1+2 (evaluate (car (Constr-args suc2+2)) defs)])
  (check-true (=α suc2+2
                  (parse-term
                   (encode-nat 4)
                   defs)))
  (check-true (=α suc1+2
                  (parse-term
                   (encode-nat 3)
                   defs)))
  (check-true (=α (evaluate (car (Constr-args suc1+2)) defs)
                  two)))

(define (ccic-Ω level)
  (let* ([elab-unk (Cast (Unk (Unk (Univ (add1 level))))
                         (Unk (Univ (add1 level)))
                         (Univ level))]
         [elab-δ
          (Lam 'x 'x elab-unk
               (App (Cast (Var 'x) elab-unk (germ (HeadPi) level '()))
                    (Cast (Var 'x) elab-unk (Unk (Univ (cΠ level))))))])
    (App elab-δ
         (Cast elab-δ (Pi '_ '_ elab-unk (Unk (Univ (cΠ level))))
               (Unk (Univ level))))))

;; This diverges as expected
#;
(parameterize ([current-variant 'gcic-g]
               [trace-eval? #t])
  (evaluate (ccic-Ω 1) '()))

(parameterize ([current-variant 'gcic-n])
  (check-equal? (evaluate (ccic-Ω 1) '()) (Err (Unk (Univ 0)))))

(parameterize ([current-variant 'gcic-shift])
  (check-equal? (evaluate (ccic-Ω 1) '()) (Err (Unk (Univ 0)))))

(check-true
 (=α
  (evaluate (parse-term
             '((λ (x : (Π (_ : (□ 1)) (□ 0))) (x ((λ (y : (□ 1)) y) (□ 0))))
               z)
             '()
             (seteqv 'z))
            '())
  (Spine (App (Spine (Var 'z)) (App (Lam 'y 'y (Univ 1) (Var 'y)) (Univ 0))))))

(check-true
 (=α
  (readback (Spine (App (Spine (Var 'z)) (App (Lam 'y 'y (Univ 1) (Var 'y)) (Univ 0))))
            '())
  (parse-term '(z (□ 0)) '() (seteqv 'z))))

(check-true
 (=α
  (normalize (parse-term
              '((λ (x : (Π (_ : (□ 1)) (□ 0))) (x ((λ (y : (□ 1)) y) (□ 0))))
                z)
              '()
              (seteqv 'z))
             '())
  (parse-term '(z (□ 0)) '() (seteqv 'z))))

(define defs (elab-defs (parse-defs `(,ind-def-nat))))

(check-true
 (=α (evaluate (parse-term
                `((λ (x : (Π (_ : (Nat)) (Nat))) x)
                  (λ (_ : (Nat))
                    (< (Nat) <== (? (□ 0)) > (< (? (□ 0)) <== (Nat) > ,(encode-nat 0)))))
                defs)
               defs)
     (parse-term
      '(λ (_ : (Nat)) (< (Nat) <== (? (□ 0)) > (< (? (□ 0)) <== (Nat) > (@ Nat zero &))))
      defs)))

(check-true
 (=α (readback (parse-term
                '(λ (_ : (Nat))
                   (< (Nat) <== (? (□ 0)) >
                      (< (? (□ 0)) <== (Nat) > (@ Nat zero &))))
                defs)
               defs)
      (parse-term
       '(λ (y : (Nat)) (@ Nat zero &))
       defs)))
