#lang racket

(require (only-in "syntax.rkt"
                  unparse-term unparse-elim-branches))
(provide (all-defined-out))

;; Frames
(struct Frame () #:transparent)
(struct FLam Frame (fparam orig-fparam body) #:transparent)
(struct FPi Frame (fparam orig-fparam body) #:transparent)
(struct FConstrParam Frame (ind-name name level pre-params post-params args) #:transparent)
(struct FConstrArg Frame (ind-name name level params pre-args post-args) #:transparent)
(struct FIndT Frame (name level pre-params post-params) #:transparent)
(struct FApp Frame (rand) #:transparent)
(struct FIndElim Frame (ind-name pred-fparam orig-pred-fparam
                                 pred-body rec-name orig-rec-name branches)
  #:transparent)
(struct FUnk Frame () #:transparent)
(struct FErr Frame () #:transparent)
(struct FCastSrc Frame (term target) #:transparent)
(struct FCastTrg Frame (term source) #:transparent)
(struct FCastTrm Frame (source target) #:transparent)

(define (evaluation-context? evalctx)
  (and (list? evalctx)
       (for/and ([frame evalctx])
         (Frame? frame))))

; precondition: (evaluation-context? evalctx)
(define (unparse-evalctx evalctx)
  (for/fold ([res '■])
            ([frame evalctx])
    (match frame
      [(FLam fparam orig-fparam body)
       `(λ (,fparam : ⦃ ,res ⦄) ,(unparse body))]
      [(FPi fparam orig-fparam body)
       `(Π (,fparam : ⦃ ,res ⦄) ,(unparse body))]
      [(FConstrParam ind-name name level pre-params post-params args)
       `(@ ,ind-name ,name
                     ,@(map unparse pre-params)
                     ⦃ ,res ⦄
                     ,@(map unparse post-params)
                     & ,@(map unparse args))]
      [(FConstrArg ind-name name level params pre-args post-args)
       `(@ ,ind-name ,name ,@(map unparse params)
                     &
                     ,@(map unparse pre-args)
                     ⦃ ,res ⦄
                     ,@(map unparse post-args))]
      [(FIndT name level pre-params post-params)
       `(,name ,level
               ,@(map unparse pre-params)
               ⦃ ,res ⦄
               ,@(map unparse post-params))]
      [(FApp rand) `(⦃ ,res ⦄ ,(unparse rand))]
      [(FIndElim ind-name z _ P f _ branches)
       `(elim ,ind-name ⦃ ,res ⦄ as (λ (,z) ,(unparse P)) rec ,f
              with . ,(unparse-branches branches))]
      [(FUnk) `(? ⦃ ,res ⦄)]
      [(FErr) `(err ⦃ ,res ⦄)]
      [(FCastSrc term target)
       `(< ,(unparse target) <== ⦃ ,res ⦄ > ,(unparse term))]
      [(FCastTrg term source)
       `(< ⦃ ,res ⦄ <== ,(unparse source) > ,(unparse term))]
      [(FCastTrm source target)
       `(< ,(unparse target) <== ,(unparse source) > ⦃ ,res ⦄)])))

(define (unparse term)
  (unparse-term term (seteqv) #f))

(define (unparse-branches branches)
  (unparse-elim-branches branches (seteqv) #f))
