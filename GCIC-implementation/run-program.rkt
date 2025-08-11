#lang racket

(require (only-in "syntax.rkt" Program parse unparse-term)
         (only-in "elaboration.rkt" elab-program unsafe-optimize?)
         (only-in "evaluation.rkt" trace-eval? evaluate)
         "examples.rkt")
(printf "=====================Begining Typecheck==================~n")
[unsafe-optimize? #t]
(match-define (Program _ defs term) (elab-program (parse prog-vec-f-append-1-0)))
(printf "=====================Elaborated Term==================~n~a~n" (unparse-term term))

(printf "=====================Beginning Evaluation==================~n")
[trace-eval? #f]
(evaluate term defs)
