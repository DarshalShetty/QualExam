#lang racket

(require rackunit)
(require "../syntax.rkt")
(require "../examples.rkt")
(require "../evaluation.rkt")

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
