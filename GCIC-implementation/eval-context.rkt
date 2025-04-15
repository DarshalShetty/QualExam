#lang racket

(require (only-in "syntax.rkt"
                  unparse-term unparse-elim-branches))
(provide (all-defined-out))

;; Frames
(struct Frame () #:transparent)
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
