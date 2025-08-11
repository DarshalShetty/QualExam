#lang racket

(provide (all-defined-out))

(require (only-in "syntax.rkt"
                  supported-variants
                  Var Univ App Lam Pi IndT Constr IndElim Branch
                  Unk UnkSurf Err Cast
                  ind-def ind-def-param-tele ind-def-constrs
                  constr-def constr-def-arg-tele
                  Program
                  unparse-defs unparse-term
                  ccic-term? *cic-telescope?
                  fresh-name subst subst-args ;subst-params
                  =α
                  get-params debug-log trace-if-param))

(require (only-in "evaluation.rkt"
                  current-variant
                  HeadPi HeadUniv HeadIndT
                  sΠ cΠ germ normalize ~))


(define (context? Γ defs)
  (and (dict? Γ)
       (immutable? Γ)
       (*cic-telescope? ccic-term? Γ defs)))

(define unsafe-optimize? (make-parameter #f))

;; Γ ⊢ t ⇝ t^ ▹ T
; precondition: (and (context? Γ)
;                    (*cic-defs? ccic-term? defs)
;                    (gcic-term? t defs (apply seteqv (dict-keys Γ))) )
; postcondition: (let-values ([(t^ T) (synth Γ t defs)])
;                  (and (ccic-term? t^ defs (apply seteqv (dict-keys Γ)))
;                       (ccic-term? T defs (apply seteqv (dict-keys Γ)))))
(define (synth Γ tᵍ defs indent)
  (trace-elab "~a Synthesizing: ~a" (make-string indent #\>) (unparse-term tᵍ (list->seteqv (map car Γ))))
  (match tᵍ
    [(Var x)
     (trace-elab "~a Applying synthesis rule: VAR" (make-string indent #\>))
     (cond
       [(dict-has-key? Γ x) (values tᵍ (dict-ref Γ x))]
       [else (error 'synth "Variable ~a not bound in context ~a" x Γ)])
     ]
    [(Univ i)
     (trace-elab "~a Applying synthesis rule: UNIV" (make-string indent #\>))
     (values tᵍ (Univ (add1 i)))]
    [(Pi x x-orig Aᵍ Bᵍ)
     (trace-elab "~a Applying synthesis rule: PROD" (make-string indent #\>))
     (match-define-values
      (Aᶜ (Univ i))
      (constrain-synth Γ Aᵍ (HeadUniv #f) defs (add1 indent)))
     (match-define-values
      (Bᶜ (Univ j))
      (constrain-synth
       (dict-set Γ x Aᶜ)
       Bᵍ (HeadUniv #f) defs (add1 indent)))
     (values (Pi x x-orig Aᶜ Bᶜ) (Univ (sΠ i j)))]
    [(Lam x x-orig Aᵍ tᵍ)
     (trace-elab "~a Applying synthesis rule: ABS" (make-string indent #\>))
     (match-define-values
      (Aᶜ (Univ i))
      (constrain-synth Γ Aᵍ (HeadUniv #f) defs (add1 indent)))
     (define-values
      (tᶜ Bᶜ)
      (synth (dict-set Γ x Aᶜ) tᵍ defs (add1 indent)))
     (values (Lam x x-orig Aᶜ tᶜ) (Pi x x-orig Aᶜ Bᶜ))]
    [(App tᵍ uᵍ)
     (trace-elab "~a Applying synthesis rule: APP" (make-string indent #\>))
     (match-define-values
      (tᶜ (Pi x _ Aᶜ Bᶜ))
      (constrain-synth Γ tᵍ (HeadPi) defs (add1 indent)))
     (define uᶜ (check Γ uᵍ Aᶜ defs (add1 indent)))
     (values (App tᶜ uᶜ) (subst `(,uᶜ) `(,x) Bᶜ))]
    [(UnkSurf i)
     (trace-elab "~a Applying synthesis rule: UNK" (make-string indent #\>))
     (values (Unk (Unk (Univ i))) (Unk (Univ i)))]
    [(IndT I i asᵍ)
     (trace-elab "~a Applying synthesis rule: IND" (make-string indent #\>))
     (define asᶜ
       (check-params Γ I i asᵍ defs (add1 indent)))
     (values (IndT I i asᶜ) (Univ i))]
    [(Constr I c i asᵍ bsᵍ)
     (trace-elab "~a Applying synthesis rule: CONS" (make-string indent #\>))
     (define asᶜ
       (check-params Γ I i asᵍ defs (add1 indent)))
     (define bsᶜ
       (check-args Γ I i c asᶜ bsᵍ defs (add1 indent)))
     (values
      (Constr I c i asᶜ bsᶜ)
      (IndT I i asᶜ))]
    [(IndElim I sᵍ z z-orig Pᵍ f f-orig branchesᵍ)
     (trace-elab "~a Applying synthesis rule: FIX" (make-string indent #\>))
     (match-define-values (sᶜ (and (IndT _ i-s asᶜ) s-typeᶜ))
                          (constrain-synth Γ sᵍ (HeadIndT I) defs (add1 indent)))
     (match-define-values (Pᶜ (and (Univ i-P) P-typeᶜ))
                          (constrain-synth (dict-set Γ z s-typeᶜ)
                                           Pᵍ (HeadUniv #f) defs (add1 indent)))
     (define Γ-branches (dict-set Γ f (Pi z z-orig s-typeᶜ Pᶜ)))
     (define branchesᶜ
       (for/list ([branchᵍ branchesᵍ])
         (match-define (Branch cₖ ys ys-orig tₖᵍ) branchᵍ)
         (define ys-var (map Var ys))
         (define Γ-branch
           (for/fold ([Γ^ Γ-branches])
                     ([y ys]
                      [y-typeᶜ (subst-args defs I i-s cₖ asᶜ ys-var)])
             (dict-set Γ^ y y-typeᶜ )))
         (define tₖ-typeᶜ
           (subst `(,(Constr I cₖ i-s asᶜ ys-var))
                  `(,z)
                  Pᶜ))
         (define tₖᶜ (check Γ-branch tₖᵍ tₖ-typeᶜ defs (add1 indent)))
         (Branch cₖ ys ys-orig tₖᶜ)))
     (values
      (IndElim I sᶜ z z-orig Pᶜ f f-orig branchesᶜ)
      (subst `(,sᶜ) `(,z) Pᶜ))]
    [_ (error 'synth "Could not synthesize a type for term ~a" tᵍ)]))

;; Γ ⊢ ãₖ ◃ Paramsₖ(I,i)[a] ⇝ aₖ
; precondition: (and (context? Γ)
;                    (symbol? I)
;                    (natural? i)
;                    (*cic-defs? ccic-term? defs)
;                    (list? asᵍ)
;                    (for/and ([param asᵍ])
;                      (gcic-term? param defs (apply seteqv (dict-keys Γ)))))
; postcondition: (and (list? (check-params Γ I i asᵍ defs))
;                     (for/and ([param (check-params Γ I i asᵍ defs)])
;                       (ccic-term? param defs (apply seteqv (dict-keys Γ)))))
(define (check-params Γ I i asᵍ defs indent)
  ;; TODO: Figure out how to interpret i.
  (trace-elab "~a Checking Parameters: ~a" (make-string indent #\>) asᵍ)
  (define def (dict-ref defs I))
  (define params-teleᶜ  (ind-def-param-tele def))
  (unless (eqv? (length asᵍ) (length params-teleᶜ))
    (error 'check-params (string-append
                        "Wrong number of parameters.~nExpected parameter types: ~a~n"
                        "Actual parameters: ~a~n")
           params-teleᶜ asᵍ))
  (for/fold ([asᶜ  '()]
             [subst-symbols '()]
             #:result asᶜ )
            ([aᵍ asᵍ]
             [(index typeᶜ) (in-dict params-teleᶜ)])
    (define Γ-closed-typeᶜ (subst asᶜ subst-symbols typeᶜ))
    (values (append asᶜ (list (check Γ aᵍ Γ-closed-typeᶜ defs (add1 indent))))
            (append subst-symbols (list index )))))

;; Γ ⊢ b̃ₘ ◃ Argsₖ(I,i,cₖ)[a,b] ⇝ bₘ
; precondition: (and (context? Γ)
;                    (symbol? I)
;                    (symbol? cₖ)
;                    (natural? i)
;                    (*cic-defs? ccic-term? defs)
;                    (list? asᶜ)
;                    (eqv? (length asᶜ) (ind-def-param-tele (dict-ref defs I)))
;                    (for/and ([param asᶜ])
;                      (ccic-term? param defs (apply seteqv (dict-keys Γ))))
;                    (list? bsᵍ)
;                    (for/and ([arg bsᵍ])
;                      (gcic-term? arg defs (apply seteqv
;                                                  (append (dict-keys Γ)
;                                                          (dict-keys
;                                                           (ind-def-param-tele
;                                                            (dict-ref defs I))))))))
; postcondition: (and (list? (check-args Γ I i cₖ asᶜ bsᵍ defs))
;                     (for/and ([arg (check-args Γ I i cₖ asᶜ bsᵍ defs)])
;                       (ccic-term? arg defs (apply seteqv (append
;                                                           (dict-keys Γ)
;                                                           (dict-keys
;                                                            (ind-def-param-tele
;                                                             (dict-ref defs I))))))))
(define (check-args Γ I i cₖ asᶜ bsᵍ defs indent)
  ;; TODO: Figure out how to interpret i.
  (trace-elab "~a Checking Arguments: ~a" (make-string indent #\>) bsᵍ)
  (define def (dict-ref defs I))
  (define params-teleᶜ  (ind-def-param-tele def))
  (define args-teleᶜ (constr-def-arg-tele
                     (dict-ref (ind-def-constrs def) cₖ)))
  (unless (eqv? (length bsᵍ) (length args-teleᶜ))
    (error 'check-args (string-append
                         "Wrong number of arguments.~nExpected argument types: ~a~n"
                         "Actual arguments: ~a~n")
           args-teleᶜ bsᵍ))
  (for/fold ([bsᶜ '()]
             [subst-symbols (map car params-teleᶜ)]
             [subst-terms asᶜ]
             #:result bsᶜ)
            ([bᵍ bsᵍ]
             [(index typeᶜ) (in-dict args-teleᶜ)])
    (define Γ-closed-typeᶜ (subst subst-terms subst-symbols typeᶜ))
    (define bᶜ (check Γ bᵍ Γ-closed-typeᶜ defs (add1 indent)))
    (values (append bsᶜ (list bᶜ ))
            (append subst-symbols (list index ))
            (append subst-terms (list bᶜ)))))

;; Γ ⊢ t ◃ T ⇝ t^
; precondition: (and (context? Γ)
;                    (*cic-defs? ccic-term? defs)
;                    (gcic-term? tᵍ defs (apply seteqv (dict-keys Γ)))
;                    (ccic-term? Sᶜ defs (apply seteqv (dict-keys Γ))))
; postcondition: (ccic-term? (check Γ tᵍ Sᶜ defs) defs (apply seteqv (dict-keys Γ)))
(define (check Γ tᵍ Sᶜ defs indent)
  (trace-elab "~a Checking term: ~a"
              (make-string indent #\>)
              (unparse-term tᵍ (list->seteqv (map car Γ))))
  (trace-elab "~a Checking type: ~a"
              (make-string indent #\>)
              (unparse-term Sᶜ (list->seteqv (map car Γ))))
  (define-values (tᶜ Tᶜ) (synth Γ tᵍ defs (add1 indent)))
  (trace-elab "~a Synthesized type: ~a"
              (make-string indent #\>)
              (unparse-term Tᶜ (list->seteqv (map car Γ))))
  (define-values (consistently-convertible? canon-Tᶜ canon-Sᶜ)
    (~ Tᶜ Sᶜ defs (map car Γ)))
  (unless consistently-convertible?
    (error 'check (string-append  "Checked type and synthesized type are not "
                                  "consistently convertible while checking for "
                                  "term ~a.~n"
                                  "Checked type=~n~a~n"
                                  "Synthesized type=~n~a~n"
                                  "Canonical checked type=~n~a~n"
                                  "Canonical synthesized type=~n~a~n")
           (unparse-term tᵍ (list->seteqv (map car Γ)))
           (unparse-term Sᶜ (list->seteqv (map car Γ)))
           (unparse-term Tᶜ (list->seteqv (map car Γ)))
           (unparse-term canon-Sᶜ (list->seteqv (map car Γ)))
           (unparse-term canon-Tᶜ (list->seteqv (map car Γ)))))
  ;; TODO: Figure out whether we can use evaluated canonical versions of Tᶜ and
  ;; Sᶜ instead below
  (cond
    [(and (=α canon-Tᶜ canon-Sᶜ) (unsafe-optimize?)) tᶜ]
    [(unsafe-optimize?) (Cast tᶜ canon-Tᶜ canon-Sᶜ)]
    [else (Cast tᶜ Tᶜ Sᶜ)]))

;; Γ ⊢ t ⇝ t^ ▹∘ T
; precondition: (and (context? Γ)
;                    (*cic-defs? ccic-term? defs)
;                    (Head? hd)
;                    (gcic-term? tᵍ defs (apply seteqv (dict-keys Γ))) )
; postcondition: (let-values ([(t^ T) (constrain-synth Γ tᵍ hd defs)])
;                  (and (ccic-term? t^ defs (apply seteqv (dict-keys Γ)))
;                       (ccic-term? Tᵍ defs (apply seteqv (dict-keys Γ)))
;                       (equal? hd (head T))))
(define (constrain-synth Γ tᵍ hd defs indent)
  (trace-elab "~a Synthesizing type with head ~a for term: ~a"
              (make-string indent #\>) hd (unparse-term tᵍ (list->seteqv (map car Γ))))
  (define-values (tᶜ Tᶜ) (synth Γ tᵍ defs (add1 indent)))
  (define norm-Tᶜ (normalize Tᶜ defs))
  (define T^
    (cond
      [(unsafe-optimize?) norm-Tᶜ]
      [else Tᶜ]))
  ;; TODO: refactor to use fewer matches
  (match hd
    [(HeadPi)
     (match norm-Tᶜ
       [(Pi _ _ _ _)
        (trace-elab "~a Applying constrained synthesis rule: INF-PROD" (make-string indent #\>))
        (values tᶜ norm-Tᶜ)]
       [(Unk (Univ i))
        #:when (natural? (cΠ i))
        (trace-elab "~a Applying constrained synthesis rule: INF-PROD?"
                    (make-string indent #\>))
        (define out-type (germ hd i defs))
        (values (Cast tᶜ T^ out-type) out-type)]
       [_ (error 'constrain-synth
                 (string-append "Expected a type with head ~a or the type (? (□ i))"
                                " where (cΠ i) >= 0, but got ~a while constrained "
                                "synthesis of term ~a")
                 hd norm-Tᶜ tᵍ)])]
    [(HeadUniv _)
     (match norm-Tᶜ
       [(Univ i)
        (trace-elab "~a Applying constrained synthesis rule: INF-UNIV"
                    (make-string indent #\>))
        (values tᶜ norm-Tᶜ)]
       [(Unk (Univ j))
        #:when (> j 0)
        (trace-elab "~a Applying constrained synthesis rule: INF-UNIV?"
                    (make-string indent #\>))
        (define i (sub1 j))
        (values (Cast tᶜ T^ (Univ i)) (Univ i))]
       [_ (error 'constrain-synth
                 (string-append "Expected a type with head ~a or the type (? (□ i))"
                                " where i > 0, but got ~a while constrained "
                                "synthesis of term ~a")
                 hd norm-Tᶜ tᵍ)])]
    [(HeadIndT I)
     (match norm-Tᶜ
       [(IndT I^ _ _)
        #:when (eqv? I I^)
        (trace-elab "~a Applying constrained synthesis rule: INF-IND"
                    (make-string indent #\>))
        (values tᶜ norm-Tᶜ)]
       [(Unk (Univ i))
        (trace-elab "~a Applying constrained synthesis rule: INF-IND?"
                    (make-string indent #\>))
        (define out-type (germ hd i defs))
        (values (Cast tᶜ T^ out-type) out-type)]
       [_ (error 'constrain-synth
                 (string-append "Expected a type with head ~a or the type (? (□ i))"
                                ", but got ~a while constrained synthesis of term ~a")
                 hd norm-Tᶜ tᵍ)])]
    [_ (error 'synth "Expected a head type, but found ~a" hd)]))

; precondition: (and (context? Γ)
;                    (*cic-defs? ccic-term? defs)
;                    (gcic-term? term defs))
; postcondition: (ccic-term? (elab-term Γ term defs) defs)
(define (elab-term Γ term defs)
  (trace-elab "***Begin Term Elaboration***")
  (define-values (term^ _) (synth Γ term defs 0))
  term^)

(define trace-elab? (make-parameter #f))
(define trace-elab
  (trace-if-param trace-elab?))

(define (elab-program prog)
  (trace-elab "***Begin Program Elaboration***")
  (match-define (Program variant-name defs term) prog)
  (parameterize ([current-variant variant-name])
    (define defs^ (elab-defs defs))
    (define term^ (elab-term '() term defs^))
    (Program variant-name defs^ term^)))

; precondition: (*cic-defs? gcic-term? defs)
; postcondition: (*cic-defs? ccic-term? (elab-defs defs))
(define (elab-defs defs)
  (trace-elab "***Begin Definitions Elaboration***")
  (for/fold ([result '()]
             #:result (begin (trace-elab "***Elaborated Definitions:***")
                             (trace-elab "~a" (unparse-defs result))
                             result))
            ([pair defs])
    (match-define (cons _ def) pair)
    (match-define (ind-def name params-tele constr-defs)
      def)
    (trace-elab "***Elaborating definition: ~a***" name)
    (define params-tele^ (elab-telescope '() params-tele result))
    (define constr-defs^
      (elab-constr-defs params-tele^
                        constr-defs
                        (dict-set result name
                                  (ind-def name params-tele^ #f))))
    (dict-set result name (ind-def name params-tele^ constr-defs^))))

; precondition: (and (context? Γ)
;                    (*cic-defs? ccic-term? prev-defs)
;                    (*cic-telescope? gcic-term? tele prev-defs))
; postcondition: (*cic-telescope? ccic-term?
;                                 (elab-telescope Γ tele prev-defs) prev-defs)
(define (elab-telescope Γ tele prev-defs)
  (for/fold ([tele^ '()]
             [Γ^ Γ]
             #:result tele^)
            ([(index type) (in-dict tele)])
    (define type^ (elab-term Γ^ type prev-defs))
    (values (append  tele^ `((,index . ,type^)))
            (dict-set Γ^ index type^))))

; precondition: (and (context? Γ)
;                    (*cic-defs? ccic-term? prev-defs)
;                    (*cic-constr-defs? gcic-term? constr-defs prev-defs))
; postcondition: (*cic-constr-defs? ccic-term?
;                                   (elab-constr-defs Γ constr-defs prev-defs)
;                                   prev-defs)
(define (elab-constr-defs Γ constr-defs prev-defs)
  (for/hasheqv ([cd (dict-values constr-defs)])
    (match-define (constr-def name args-tele) cd)
    (define args-tele^ (elab-telescope Γ args-tele prev-defs))
    (values name (constr-def name args-tele^))))
