#lang racket

(require (only-in "syntax.rkt"
                  parse unparse-term Program))
(require (only-in "evaluation.rkt"
                  evaluate evaluate-subterms current-variant))
(require (only-in "elaboration.rkt"
                 elab-program))

(provide run)

(define (run program #:pretty? [pretty? #f] #:force? [force? #f])
  (match-define (Program variant-name defs term)
    (elab-program (parse program)))
  (define interp (if force? evaluate-subterms evaluate))
  (parameterize ([current-variant variant-name])
    (define result (interp term defs))
    (cond
      [pretty? (unparse-term result)]
      [else result])))
