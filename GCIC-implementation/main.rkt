#lang racket

(require (only-in "syntax.rkt"
                  parse unparse-term Program))
(require (only-in "evaluation.rkt"
                  normalize current-variant))
(require (only-in "elaboration.rkt"
                 elab-program))

(provide run)

(define (run program #:pretty? [pretty? #f])
  (match-define (Program variant-name defs term)
    (elab-program (parse program)))
  (parameterize ([current-variant variant-name])
    (define result (normalize term defs))
    (cond
      [pretty? (unparse-term result)]
      [else result])))
