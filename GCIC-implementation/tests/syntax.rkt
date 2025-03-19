#lang racket

(require rackunit)
(require "../syntax.rkt")
(require "../examples.rkt")

(check-equal? (parse '((variant gcic-n) (? 1)))
              (Program 'gcic-n '() (UnkSurf 1)))

(check-equal? (Program-term
               (parse prog-nat-one))
              (Constr 'Nat 'succ '() (list (Constr 'Nat 'zero '() '()))))

(check-equal? (last (unparse (parse prog-nat-one))) (last prog-nat-one))

(check-true (gcic-program? (parse prog-nat-one)))

(check-equal? (Program-term
               (parse prog-list-nat-one))
              (Constr 'List 'cons
                      (list (IndT 'Nat '()))
                      (list
                       (Constr 'Nat 'succ '()
                               (list (Constr 'Nat 'zero '() '())))
                       (Constr 'List 'null
                               (list (IndT 'Nat '())) '()))))

(check-equal? (last (unparse (parse prog-list-nat-one))) (last prog-list-nat-one))

(check-true (gcic-program? (parse prog-list-nat-one)))

(check-equal? (last (unparse (parse prog-omega))) (last prog-omega))

(check-true (gcic-program? (parse prog-omega)))

(check-equal? (last (unparse (parse prog-add-2-3))) (last prog-add-2-3))

(check-true (gcic-program? (parse prog-add-2-3)))

(check-equal? (last (unparse (parse prog-eq-nat-2))) (last prog-eq-nat-2))

(check-true (gcic-program? (parse prog-eq-nat-2)))

(define term-subst-test
  (Lam 'f
       (Pi '_  (Var 'X) (Var 'X))
       (Lam 'X
            (Univ 0)
            (Lam 'x
                 (Var 'X)
                 (App (Var 'f) (Var 'x))))))

(check-true (=α (subst (IndT 'Nat '()) 'X term-subst-test)
                (Lam 'f
                     (Pi '_ (IndT 'Nat '()) (IndT 'Nat '()))
                     (Lam 'X
                          (Univ 0)
                          (Lam 'x
                               (Var 'X)
                               (App (Var 'f) (Var 'x)))))))

(check-true (=α (subst (Var 'f) 'X term-subst-test)
                (Lam 'f^
                     (Pi '_ (Var 'f) (Var 'f))
                     (Lam 'X
                          (Univ 0)
                          (Lam 'x
                               (Var 'X)
                               (App (Var 'f^) (Var 'x)))))))

;;TODO:
;;- Add tests to ensure all errors in parse are triggered
