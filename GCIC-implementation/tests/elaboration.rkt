#lang racket

(require (except-in rackunit
                    check))

(require "../syntax.rkt"
         "evaluation.rkt"
         "../evaluation.rkt"
         "../examples.rkt"
         "../elaboration.rkt")

(check-true (ccic-program? (elab-program (parse prog-check-arg))))

(check-true (ccic-program? (elab-program (parse prog-nat-one))))
(check-true (ccic-program? (elab-program (parse prog-list-nat-one))))
(check-true (ccic-program? (elab-program (parse prog-list-append-12-34))))

(check-true (ccic-program? (elab-program (parse prog-scope))))
(check-true (ccic-program? (elab-program (parse prog-add-2-3))))
(check-true (ccic-program? (elab-program (parse prog-eq-nat-2))))
(check-true (ccic-program? (elab-program (parse prog-vec-f-12))))
;; TODO: make this test case work
(parameterize ([trace-elab? #f]
               [trace-eval? #t])
  (check-true (ccic-program? (elab-program (parse prog-vec-f-append-12-34)))))
#;
(parameterize ([debug? #f]
               [trace-elab? #t])
  (check-true (ccic-program? (elab-program (parse prog-vec-μ-12)))))

(for* ([variant '(gcic-n gcic-shift gcic-g)]
       [i (in-range 3)])
  (parameterize ([current-variant variant]
                 [debug? #f]
                 [trace-eval? #f]
                 [trace-elab? #f])
    (cond
      [(and (eqv? i 0) (memv variant '(gcic-n gcic-shift)))
       (check-exn exn:fail? (λ () (elab-term '() (parse-term (term-Ω i) '()) '())))]
      [else
       (define actual (elab-term '() (parse-term (term-Ω i) '()) '()))
       (define expected (ccic-Ω i))
       (check-true (=α actual expected))])))
