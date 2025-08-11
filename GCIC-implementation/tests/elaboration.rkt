#lang racket

(require (except-in rackunit
                    check))

(require "../syntax.rkt"
         "evaluation.rkt"
         "../evaluation.rkt"
         "../examples.rkt"
         "../elaboration.rkt")

(unsafe-optimize? #t)

(check-true (ccic-program? (elab-program (parse prog-check-arg))))

(check-true (ccic-program? (elab-program (parse prog-nat-one))))
(check-true (ccic-program? (elab-program (parse prog-norm-in-elab))))
(check-true (ccic-program? (elab-program (parse prog-list-nat-one))))
(check-exn #rx"^check:" (λ () (elab-program (parse prog-list-univ-err))))
(check-true (ccic-program? (elab-program (parse prog-list-univ))))
(check-true (ccic-program? (elab-program (parse prog-list-univ-weird))))
(check-true (ccic-program? (elab-program (parse prog-list-append-12-34))))
(check-true (ccic-program? (elab-program (parse prog-list-length-123))))

(check-true (ccic-program? (elab-program (parse prog-scope))))
(check-true (ccic-program? (elab-program (parse prog-add-2-3))))
(check-true (ccic-program? (elab-program (parse prog-leb-2-3))))
(check-true (ccic-program? (elab-program (parse prog-eq-nat-2))))
(check-true (ccic-program? (elab-program (parse prog-one-zero?))))
(check-true (ccic-program? (elab-program (parse prog-one-zero?-unk))))
(check-true (ccic-program? (elab-program (parse prog-inj-eq-nat))))
(check-true (ccic-program? (elab-program (parse prog-proj-eq-nat))))
(check-true (ccic-program? (elab-program (parse prog-sym-eq-nat))))
(check-true (ccic-program? (elab-program (parse prog-refl-eq-nat))))
(check-true (ccic-program? (elab-program (parse prog-trans-eq-nat))))
(check-true (ccic-program? (elab-program (parse prog-false-O-S))))
(check-true (ccic-program? (elab-program (parse prog-n=0+n))))
(check-true (ccic-program? (elab-program (parse prog-head-f))))
(check-true (ccic-program? (elab-program (parse prog-vec-f-12))))
(check-true (ccic-program? (elab-program (parse prog-subst-vec-f))))
(check-true (ccic-program? (elab-program (parse prog-vec-f-filter-leb4-35))))
(check-true (ccic-program? (elab-program (parse prog-example-1))))
(check-true (ccic-program? (elab-program (parse prog-example-1-err))))
(check-true (ccic-program? (elab-program (parse prog-compose-≤3-length-123))))
(check-true (ccic-program? (elab-program (parse prog-vec-f-append-12-34))))
(check-true (ccic-program? (elab-program (parse prog-vec-μ-12))))
(check-true (ccic-program? (elab-program (parse prog-vec-μ-append-12-34))))
(check-true (ccic-program? (elab-program (parse prog-blame))))
(check-true (ccic-program? (elab-program (parse prog-fin-3))))
(check-exn #rx"^check:" (λ () (elab-program (parse prog-fin-3-typefail))))
(check-true (ccic-program? (elab-program (parse prog-false-fin-O))))
(check-true (ccic-program? (elab-program (parse prog-subst-fin-f))))
(check-true (ccic-program? (elab-program (parse prog-nth-1-34))))
(check-true (ccic-program? (elab-program (parse prog-nth-3-1234))))

(for* ([variant '(gcic-n gcic-shift gcic-g)]
       [i (in-range 3)])
  (parameterize ([current-variant variant]
                 [unsafe-optimize? #f]
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
