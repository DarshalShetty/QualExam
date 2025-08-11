#lang racket

(require rackunit)
(require "../syntax.rkt")
(require "../examples.rkt")

(define (check-program program)
  (define parsed (parse program))
  (check-equal? (last (unparse parsed)) (last program))

  (check-true (gcic-program? parsed)))

(check-equal? (parse '((variant gcic-n) (? 1)))
              (Program 'gcic-n '() (UnkSurf 1)))

(check-equal? (Program-term
               (parse prog-nat-one))
              (Constr 'Nat 'succ 0 '() (list (Constr 'Nat 'zero 0 '() '()))))

(check-program prog-nat-one)

(check-program prog-norm-in-elab)

(check-equal? (Program-term
               (parse prog-list-nat-one))
              (Constr 'List 'cons 0
                      (list (IndT 'Nat 0 '()))
                      (list
                       (Constr 'Nat 'succ 0 '()
                               (list (Constr 'Nat 'zero 0 '() '())))
                       (Constr 'List 'null 0
                               (list (IndT 'Nat 0 '())) '()))))

(check-program prog-list-nat-one)

(check-program prog-list-univ-err)

(check-program prog-list-univ)

(check-program prog-list-univ-weird)

(check-program prog-list-append-12-34)

(check-program prog-list-length-123)

(check-program prog-omega)

(check-program prog-scope)

(check-program prog-add-2-3)

(check-program prog-leb-2-3)

(check-program prog-eq-nat-2)

(check-program prog-one-zero?)

(check-program prog-one-zero?-unk)

(check-program prog-inj-eq-nat)

(check-program prog-proj-eq-nat)

(check-program prog-false-O-S)

(check-program prog-sym-eq-nat)

(check-program prog-trans-eq-nat)

(check-program prog-vec-f-12)

(check-program prog-head-f)

(check-program prog-vec-f-filter-leb4-35)

(check-program prog-example-1)

(check-program prog-example-1-err)

(check-program prog-compose-≤3-length-123)

(check-program prog-vec-f-append-12-34)

(check-program prog-vec-μ-12)

(check-program prog-check-arg)

(check-program prog-blame)

(check-program prog-fin-3)

(check-program prog-fin-3-typefail)

(check-program prog-false-fin-O)

(check-program prog-subst-fin-f)

(check-program prog-nth-1-34)

(check-program prog-nth-3-1234)

(define term-subst-test
  (Lam 'f 'f
       (Pi '_ '_ (Var 'X) (Var 'X))
       (Lam 'X 'X
            (Univ 0)
            (Lam 'x 'x
                 (Var 'X)
                 (App (Var 'f) (Var 'x))))))

(let ([actual (subst `(,(Univ 1)) '(X) term-subst-test)])
  (check-true (ccic-term? actual '()))
  (check-true (=α actual
                  (Lam 'f 'f
                       (Pi '_ '_ (Univ 1) (Univ 1))
                       (Lam 'X 'X
                            (Univ 0)
                            (Lam 'x 'x
                                 (Var 'X)
                                 (App (Var 'f) (Var 'x))))))))

(let ([actual (subst `(,(Var 'f)) '(X) term-subst-test)])
  (check-true (ccic-term? actual '() (seteqv 'f)))
  (check-true (=α actual
                  (Lam 'f^ 'f
                       (Pi '_ '_ (Var 'f) (Var 'f))
                       (Lam 'X 'X
                            (Univ 0)
                            (Lam 'x 'x
                                 (Var 'X)
                                 (App (Var 'f^) (Var 'x))))))))

(define parsed-term-sum (parse-term fun-add (parse-defs `(,ind-def-nat))))
(let ([actual (subst `(,(Var 'y)) '(m) parsed-term-sum)])
  (check-true (ccic-term? actual
                          (parse-defs `(,ind-def-nat))
                          (seteqv 'y)))
  (check-equal? actual parsed-term-sum))

(let ([actual (subst `(,(Var 'y)) '(n) parsed-term-sum)])
  (check-true (ccic-term? actual
                          (parse-defs `(,ind-def-nat))
                          (seteqv 'y)))
  (check-not-equal? actual parsed-term-sum)
  (check-true (=α actual parsed-term-sum)))

(let ([actual (subst `(,(Var 'z) ,(Var 'y)) '(m n) parsed-term-sum)])
  (check-true (ccic-term? actual
                          (parse-defs `(,ind-def-nat))
                          (seteqv 'y)))
  (check-not-equal? actual parsed-term-sum)
  (check-true (=α actual parsed-term-sum)))

(check-equal? (car
               (subst-elim-branches
                `(,(Var 'y)) '(n)
                (list
                 (Branch 'succ '(n) '(n) (Var 'n)))))
              (Branch 'succ '(n) '(n) (Var 'n)))

(let ([b (Branch 'succ '(l m n o) '(l m n o)
                 (App (Var 'l)
                      (App (Var 'm)
                           (App (Var 'n)
                                (App (Var 'o)
                                     (Var 'p))))))])
  (check-equal? (car
                 (subst-elim-branches
                  `(,(Var 'w) ,(Var 'x) ,(Var 'y) ,(Var 'z)) '(l m n o)
                  (list b)))
                b)
  (check-equal? (car
                 (subst-elim-branches
                  `(,(Var 'x) ,(Var 'y) ,(Var 'z)) '(m n o)
                  (list b)))
                b)
  (let ([actual (car
                 (subst-elim-branches
                  `(,(Var 'v) ,(Var 'w) ,(Var 'x) ,(Var 'y) ,(Var 'p)) '(l m n o p)
                  (list b)))])
    (check-not-equal? actual b)
    (check-true (elim-branches-*α =α `(,actual) `(,b) (list) (list)))))

(define ind-defs-subst-test
  (parse-defs
   `(,ind-def-nat
     ,ind-def-list
     (data I (a : (□ 1)) (b : (List a)) (c : (Π (_ : a) b))
           ([iconstr (d : (List b)) (e : (Π (f : (List d)) (c f)))])))))

(let ([actual (subst-params ind-defs-subst-test
                                'I 0
                                `(,(Univ 0)
                                  ,(Constr 'List 'cons 1 `(,(Univ 0))
                                           `(,(IndT 'Nat 0 '())))
                                  ,(Lam 'x 'x (Univ 0) (Var 'x))))])
  (check-true (for/and ([a actual])
                (ccic-term? a ind-defs-subst-test)))
  (check-true (for/and ([a actual]
                        [e `(,(Univ 1)
                             ,(IndT 'List 0 `(,(Univ 0)))
                             ,(Pi 'f 'f (Univ 0)
                                  (Constr 'List 'cons 1
                                          `(,(Univ 0))
                                          `(,(IndT 'Nat 0 '())))))])
                (=α a e))))

(let ([actual (subst-args ind-defs-subst-test
                                'I 0 'iconstr
                                `(,(Univ 0)
                                  ,(Constr 'List 'cons 1
                                           `(,(Univ 0))
                                           `(,(IndT 'Nat 0 '())))
                                  ,(Lam 'x 'x (Univ 0) (Var 'x)))
                                `(,(Constr 'List 'cons 1
                                           `(,(IndT 'Nat 0 '()))
                                           `(,(parse-term term-two
                                                          ind-defs-subst-test)))
                                  ,(Lam 'f 'f
                                        (IndT 'List 1
                                              `(,(Constr 'List 'cons 1
                                                         `(,(IndT 'Nat 0 '()))
                                                         `(,(parse-term
                                                             term-two
                                                             ind-defs-subst-test)))))
                                        (Var 'f))))])
  (check-true (for/and ([a actual])
                (ccic-term? a ind-defs-subst-test)))
  (check-true (for/and ([a actual]
                        [e `(,(IndT 'List 0
                                    `(,(Constr 'List 'cons 1 `(,(Univ 0))
                                               `(,(IndT 'Nat 0 '())))))
                             ,(Pi 'f 'f
                                  (IndT 'List 0
                                        (list (Constr 'List 'cons 1
                                                      `(,(IndT 'Nat 0 '()))
                                                      `(,(parse-term
                                                          term-two
                                                          ind-defs-subst-test)))))
                                  (App (Lam 'x 'x (Univ 0) (Var 'x)) (Var 'f))))])
                (=α a e))))

;;TODO: - Add tests to ensure all errors in parse are triggered
