#lang racket

(require (only-in "syntax.rkt"
                  supported-variants
                  Var Univ App Lam Pi IndT Constr IndElim Branch
                  Unk Err Cast
                  Spine Spine?
                  ind-def
                  unparse-term
                  ~α
                  fresh-name subst subst-args
                  get-params debug-log trace-if-param))
(require (only-in "eval-context.rkt"
                  FLam FPi FConstrParam FConstrArg FIndT
                  FApp FIndElim FUnk FErr FCastSrc FCastTrg FCastTrm
                  unparse-evalctx))
(provide (all-defined-out))

(define current-variant (make-parameter 'unset-variant))
(define (set-variant! variant^)
  (cond
    [(memv variant^ supported-variants) (current-variant variant^)]
    [else (error 'set-variant
                 "Variant '~a' not supported. Expected one of ~a"
                 variant^ supported-variants)]))


(define (sΠ i j)
  (match (current-variant)
    [(or 'gcic-g 'gcic-n) (max i j)]
    ['gcic-shift (add1 (max i j))]))

(define (cΠ i)
  (match (current-variant)
    [(or 'gcic-n 'gcic-shift) (sub1 i)]
    ['gcic-g i]))

(define (cΠ-inv i)
  (match (current-variant)
    [(or 'gcic-n 'gcic-shift) (add1 i)]
    ['gcic-g i]))

(struct Head () #:transparent)
(struct HeadPi Head () #:transparent)
(struct HeadUniv Head (level) #:transparent)
(struct HeadIndT Head (name) #:transparent)

;; precondition: (ccic-type? t)
;; postcondition: (Head? (head t))
(define (head t)
  (match t
    [(Pi _ _ _ _) (HeadPi)]
    [(Univ l) (HeadUniv l)]
    [(IndT name _ _) (HeadIndT name)]
    [_ (error 'head "Expected a CastCIC type, but got: ~a" t)]))

;; precondition: (ccic-type? t)
(define (ccic-type? t)
  (match t
    [(or (Pi _ _ _ _)
         (Univ _)
         (IndT _ _ _))
     #t]
    [_ #f]))

;; precondition: (and (Head? hd)
;;                    (natural? level)
;;                    (*cic-defs? ccic-term? defs))
;; postcondition: (ccic-term? (germ hd level defs))
(define (germ hd level defs)
  (match hd
    [(HeadUniv j) #:when (< j level) (Univ j)]
    [(HeadUniv j) (Err (Univ level))]
    [(HeadIndT name)
     (IndT name level (map (λ (p) (Unk p)) (get-params defs name level)))]
    [(HeadPi)
     #:when (>= (cΠ level) 0)
     (Pi '_ '_ (Unk (Univ (cΠ level))) (Unk (Univ (cΠ level))))]
    [(HeadPi) (Err (Univ level))]))

(define (germ? term level)
  (match term
    [(Univ i)
     #:when (< i level)
     #t]
    [(Err (Univ i))
     #:when (eqv? i level)
     #t]
    [(Pi _ _ (Unk (Univ i)) (Unk (Univ i)))
     #:when (eqv? i (cΠ level))
     #t]
    [(IndT _ i params)
     #:when (eqv? i level)
     (for/and ([param params])
       (match param
         [(Unk _) #t]
         [_ #f]))]
    [_
     (debug-log (format "Not a germ at level ~a: ~a" level term))
     #f]))

;; Preconditons: (ccic-term? term)
(define (canonical-term? term)
  (match term
    [(Lam _ _ A _) (canonical-term? A)]
    [(Pi _ _ A _) (canonical-term? A)]
    [(Constr _ _ _ params args)
     (for/and ([t (append params args)])
       (canonical-term? t))]
    [(Univ _) #t]
    [(IndT _ _ params)
     (for/and ([param params])
       (canonical-term? param))]
    [(Spine neut) (neutral-term? neut)]
    [(Unk t) (canon-unk-err-type? t)]
    [(Err t) (canon-unk-err-type? t)]
    [(Cast term source (Unk (Univ level)))
     (and (germ? source level) (canonical-term? term))]
    [_
     (debug-log (format "Not a canonical term: ~a" term))
     #f]))

;; Preconditons: (ccic-term? term)
(define (canon-unk-err-type? term)
  (match term
    [(Univ _) #t]
    [(IndT _ _ params)
     (for/and ([param params])
       (canonical-term? param))]
    [(or (Unk (Univ _)) (Err (Univ _))) #t]
    [_
     (debug-log
      (format
       "Not a canonical type used with Unk or Err: ~a"
       term))
     #f]))

;; Preconditons: (ccic-term? term)
(define (neutral-term? term)
  (match term
    [(Var _) #t]
    [(App rator _) (neutral-term? rator)]
    [(IndElim _ scrut _ _ _ _ _ _) (neutral-term? scrut)]
    [(or (Unk t) (Err t)) (neutral-term? t)]
    [(Lam _ _ A _) (neutral-term? A)]
    [(Pi _ _ A _) (neutral-term? A)]
    [(Constr _ _ _ params args) (neutral-sequence? (append params args))]
    [(IndT _ _ params) (neutral-sequence? params)]
    [(Cast term source target)
     (match source
       [_ #:when (neutral-term? source) #t]
       [(Unk (Univ _)) (neutral-term? term)]
       [(Univ _) (neutral-term? target)]
       [(Pi _ _ A _)
        #:when (canonical-term? A)
        (match target
          [(Pi _ _ _ _) (neutral-term? term)]
          [_ (neutral-term? target)])]
       [(IndT _ _ paramsS)
        #:when (for/and ([param paramsS])
                 (canonical-term? param))
        (match target
          [(IndT _ _ paramsT)
           #:when (for/and ([param paramsT])
                    (canonical-term? param))
           (neutral-term? term)]
          [_ (neutral-term? target)])]
       [_
        (debug-log
         (format
          "Invalid source type of a neutral cast: ~a"
          source))
        #f])]
    [_
     (debug-log (format "Not a neutral term: ~a" term))
     #f]))

;; Preconditons: (and (list? ts)
;;                    (for/and ([term ts])
;;                      (ccic-term? term)))
(define (neutral-sequence? ts)
  (cond
    [(null? ts) #t]
    [(Spine? (car ts)) (neutral-sequence? (car ts))]
    [(canonical-term? (car ts)) (neutral-sequence? (cdr ts))]
    [else #f]))

; ∃ scope, defs . (and (ccic-term? term defs scope) (not (canonical-term? term))
;                      (ccic-term? (reduce-if-principal defs term) defs scope))
(define (reduce-if-principal defs term)
  (match term
    ;; CIC rules
    [(App (Lam x _ A t) u)
     (trace-eval "Applying principal reduction rule PROD-BETA")
     (subst `(,u) `(,x) t)]
    [(IndElim I (Constr I cₖ level as bs) z orig-z P f orig-f branches)
     (trace-eval "Applying principal reduction rule IND-BETA")
     (match-define (Branch _ ys _ tₖ) (findf
                                       (λ (b)
                                         (match-define (Branch cname _ _ _) b)
                                         (eqv? cname cₖ))
                                       branches))
     (define x (fresh-name 'x))
     (subst bs ys
            (subst `(,(Lam x x (IndT I level as)
                           (IndElim I (Var x) z orig-z P f orig-f branches)))
                   `(,f) tₖ))]

    ;; Propagation rules for ? and err
    [(Unk (Pi x orig-x A B))
     (trace-eval "Applying principal reduction rule PROD-UNK")
     (Lam x orig-x A (Unk B))]
    [(Err (Pi x orig-x A B))
     (trace-eval "Applying principal reduction rule PROD-ERR")
     (Lam x orig-x A (Err B))]
    [(IndElim I (Unk (IndT I l as)) z orig-z P f orig-f branches)
     (trace-eval "Applying principal reduction rule MATCH-UNK")
     (Unk (subst `(,(Unk (IndT I l as))) `(,z) P))]
    [(IndElim I (Err (IndT I l as)) z orig-z P f orig-f branches)
     (trace-eval "Applying principal reduction rule MATCH-ERR")
     (Err (subst `(,(Err (IndT I l as))) `(,z) P))]
    [(Cast (Unk (IndT I l as)) (IndT I l as^^) (IndT I l as^))
     (trace-eval "Applying principal reduction rule IND-UNK")
     (Unk (IndT I l as^))]
    [(Cast (Err (IndT I l as)) (IndT I l as^^) (IndT I l as^))
     (trace-eval "Applying principal reduction rule IND-ERR")
     (Err (IndT I l as^))]
    [(Cast (Unk (Unk (Univ l))) (Unk (Univ l)) X)
     (trace-eval "Applying principal reduction rule DOWN-UNK")
     (Unk X)]
    [(Cast (Err (Unk (Univ l))) (Unk (Univ l)) X)
     (trace-eval "Applying principal reduction rule DOWN-ERR")
     (Err X)]

    ;; Success rules for cast
    [(Cast (Lam x orig-x A t) (Pi z orig-z A1 B1) (Pi y orig-y A2 B2))
     (trace-eval "Applying principal reduction rule PROD-PROD")
     (define fresh-y (fresh-name y))
     (Lam fresh-y fresh-y A2
          (Cast (subst `(,(Cast (Var fresh-y) A2 A)) `(,x) t)
                (subst `(,(Cast (Var fresh-y) A2 A1)) `(,z) B1)
                B2))]
    [(Cast A (Univ i) (Univ i))
     (trace-eval "Applying principal reduction rule UNIV-UNIV")
     A]
    [(Cast (Constr I c level as bs) (IndT I level as1) (IndT I level as2))
     (trace-eval "Applying principal reduction rule IND-IND")
     ;; NOTE: Meven agrees that this way of implementing the IND-IND rule should
     ;; be correct compared to the ambiguous way in which it is stated in the paper.
     (define bs^
       (for/list ([b bs]
                  [src (subst-args defs I level c as1 bs)]
                  [trg (subst-args defs I level c as2 bs)])
         (Cast b src trg)))
     (Constr I c level as2 bs^)]

    ;; Failure rules for casts
    [(Cast t T T^)
     #:when (and (ccic-type? T) (ccic-type? T^) (not (equal? (head T) (head T^))))
     (trace-eval "Applying principal reduction rule HEAD-ERR")
     (Err T^)]
    [(Cast t (Err (Univ _)) T)
     (trace-eval "Applying principal reduction rule DOM-ERR")
     (Err T)]
    [(Cast t T (Err (Univ level)))
     #:when (ccic-type? T)
     (trace-eval "Applying principal reduction rule CODOM-ERR")
     (Err (Err (Univ level)))]

    ;; Rules for casts with ?
    [(Cast (Cast t T (Unk (Univ i))) (Unk (Univ i)) X)
     #:when (and (germ? T i) (not (equal? T (Err (Univ i)))))
     (trace-eval "Applying principal reduction rule UP-DOWN")
     (Cast t T X)]
    [(Cast t A (Unk (Univ i)))
     ;; TODO: Test a program which executes this case
     #:when (size-err-check A i)
     (trace-eval "Applying principal reduction rule SIZE-ERR")
     (Err (Unk (Univ i)))]
    ;; TODO: ensure whether the next two cases really don't need the
    ;; precondition checks specified in the paper.
    [(Cast t (and S (IndT I level as)) (Unk (Univ i)))
     (trace-eval "Applying principal reduction rule IND-GERM")
     (let ([G (germ (HeadIndT I) i defs)])
       (Cast (Cast t S G) G (Unk (Univ i))))]
    [(Cast t (and S (Pi x orig-x A B)) (Unk (Univ i)))
     (trace-eval "Applying principal reduction rule PROD-GERM")
     (let ([G (germ (HeadPi) i defs)])
       (Cast (Cast t S G) G (Unk (Univ i))))]

    ;; Spine expansion rules
    [(Var x)
     (trace-eval "Applying principal reduction rule SPINE-VAR")
     (Spine (Var x))]
    [(App (Spine neut) t)
     (trace-eval "Applying principal reduction rule SPINE-APP")
     (Spine (App neut t))]
    [(IndElim I (Spine neut) z orig-z P f orig-f branches)
     (trace-eval "Applying principal reduction rule SPINE-MATCH")
     (Spine (IndElim I neut z orig-z P f orig-f branches))]
    [(Unk (Spine neut))
     (trace-eval "Applying principal reduction rule SPINE-UNK")
     (Spine (Unk neut))]
    [(Err (Spine neut))
     (trace-eval "Applying principal reduction rule SPINE-ERR")
     (Spine (Err neut))]
    [(Lam x x-orig (Spine neut) body)
     (trace-eval "Applying principal reduction rule SPINE-LAM")
     (Spine (Lam x x-orig neut body))]
    [(Pi x x-orig (Spine neut) body)
     (trace-eval "Applying principal reduction rule SPINE-PI")
     (Spine (Pi x x-orig neut body))]
    [(Constr ind-name constr-name level params args)
     #:when (findf Spine? (append params args))
     (trace-eval "Applying principal reduction rule SPINE-CONSTR")
     (Spine (Constr ind-name constr-name level params args))]
    [(IndT name level params)
     #:when (findf Spine? params )
     (trace-eval "Applying principal reduction rule SPINE-IND")
     (Spine (IndT name level params))]
    [(Cast t (Spine neut) target)
     (trace-eval "Applying principal reduction rule SPINE-CAST-SRC")
     (Spine (Cast t neut target))]
    [(Cast t source (Spine neut))
     (trace-eval "Applying principal reduction rule SPINE-CAST-TGT")
     (Spine (Cast t source neut))]
    [(Cast (Spine neut) source target)
     (trace-eval "Applying principal reduction rule SPINE-CAST-TRM")
     (Spine (Cast neut source target))]

    [_
     (trace-eval "Cannot apply any principal reduction rule")
     (debug-log (format "Not a principal reduction: ~a" term))
     #f]))

;; Checks whether the smallest j such that (germ? type j)=#t is greater than
;; level.
(define (size-err-check type level)
  (match type
    [(Univ i)
     ;; smallest j such that (germ? (Univ i) j)=#t is (add1 i)
     (> (add1 i) level)]
    [(Err (Univ i))
     ;; smallest j such that (germ? (Err (Univ i)) j)=#t is i
     (> i level)]
    [(Pi _ _ (Unk (Univ i)) (Unk (Univ i)))
     ;; smallest j such that (germ? (Pi _ _ (Unk (Univ i)) (Unk (Univ i))) j)=#t
     ;; is (cΠ-inv j)
     (> (cΠ-inv i) level)]
    [(IndT _ i params)
     ;; smallest j such that (germ? (IndT _ i params) j)=#t is i
     (> i level)]
    [_
     (debug-log (format (string-append
                          "No smallest level j found such that (germ? ~a j)=#t "
                          "which is less than ~a")
                        type level))
     #f]))

;; When evaluate returns a pair, it means that a pair of stuck term and its
;; surrounding evaluation context was found.
; precondition: (and (*cic-defs? ccic-term? defs)
;                    (ccic-term? t defs))
; postcondition: (or (canonical-term? (evaluate t defs))
;                    (and (pair? (evaluate t defs))
;                         (evaluation-context? (car (evaluate t defs)))
;                         (ccic-term? (cdr (evaluate t defs)))))
(define (evaluate t defs)
  (trace-eval "***Beginning Evaluation***")
  (refocus t '() defs))

; precondition: (and (*cic-defs? ccic-term? defs)
;                    (or (canonical-term? t)
;                        (and (pair? t)
;                             (evaluation-context? (car t))
;                             (ccic-term? (cdr t)))))
; postcondition: (or (canonical-term? (iterate t defs))
;                    (and (pair? (iterate t defs))
;                         (evaluation-context? (car (iterate t defs)))
;                         (ccic-term? (cdr (iterate t defs)))))
(define (iterate t defs)
  (trace-eval "***Iterating***")
  (cond
    [(not (pair? t))
     (trace-eval "Evaluation result: ~a~n" (pretty-format (unparse-term t (seteqv) #f)))
     t]
    [else
     (match-define (cons evalctx potential-redex) t)
     (cond
       [(reduce-if-principal defs potential-redex)
        => (λ (reduct)
             (trace-eval "Principal Reduction: ~a~n⇝~n~a~n"
                         (pretty-format (unparse-term potential-redex (seteqv) #f))
                         (pretty-format (unparse-term reduct (seteqv) #f)))
             (refocus reduct evalctx defs))]
       [else
        (trace-eval "Stuck Term: ~a~n"
                    (pretty-format (unparse-term potential-redex (seteqv) #f)))
        (trace-eval "Context: ~a~n" (pretty-format (unparse-evalctx evalctx)))
        t])]))

; precondition: (and (*cic-defs? ccic-term? defs)
;                    (evaluation-context? evalctx)
;                    (ccic-term? t defs))
; postcondition: (or (canonical-term? (refocus t evalctx defs))
;                    (and (pair? (refocus t evalctx defs))
;                         (evaluation-context? (car (refocus t evalctx defs)))
;                         (ccic-term? (cdr (refocus t evalctx defs)))))
(define (refocus t evalctx defs)
  (trace-eval "***Refocusing***~n")
  (trace-eval "Term:~a~n" (pretty-format (unparse-term t (seteqv) #f)))
  (trace-eval "Context:~a~n" (pretty-format (unparse-evalctx evalctx)))
  (match t
    [v
     ;; TODO: canonical-term? checks whether the term in a Spine node is a
     ;; neutral-term?. Since a Spine node is only constructed during evaluation,
     ;; the term inside this node will satisfy neutral-term? by construction.
     ;; Therefore, we should try using a version of canonical-term? which
     ;; returns #t for a Spine node without checking whether the term inside the
     ;; Spine satisfies neutral-term? which would save some time.
     #:when (canonical-term? v)
     (refocus-aux evalctx v defs)]

    ;; cases corresponding to neutral-term? cases
    [(Var x) (iterate `(,evalctx . ,t) defs)]
    [(App rator rand) (refocus rator (cons (FApp rand) evalctx) defs)]
    [(IndElim ind-name scrut z orig-z P f orig-f branches)
     (refocus scrut
              (cons
               (FIndElim ind-name z orig-z P f orig-f branches)
               evalctx)
              defs)]
    [(Unk T)
     (refocus T (cons (FUnk) evalctx) defs)]
    [(Err T)
     (refocus T (cons (FErr) evalctx) defs)]
    [(Lam x x-orig T body)
     (refocus T (cons (FLam x x-orig body) evalctx) defs)]
    [(Pi x x-orig T body)
     (refocus T (cons (FPi x x-orig body) evalctx) defs)]
    [(Constr ind-name constr-name level
             (cons first-param rest-params) args)
     (refocus first-param
              (cons
               (FConstrParam ind-name constr-name level
                             '() rest-params args)
               evalctx)
              defs)]
    [(Constr ind-name constr-name level '()
             (cons first-arg rest-args))
     (refocus first-arg
              (cons
               (FConstrArg ind-name constr-name level
                           '() '() rest-args)
               evalctx)
              defs)]
    [(IndT name level (cons first-param rest-params))
     (refocus first-param
              (cons (FIndT name level '() rest-params) evalctx)
              defs)]
    [(Cast term source target)
     (refocus source (cons (FCastSrc term target) evalctx) defs)]

    [_ (error 'refocus "Unexpected term:~n~a~nContext:~a~n"
              (pretty-format (unparse-term t (seteqv) #f))
              (pretty-format (unparse-evalctx evalctx)))]))

; precondition: (and (*cic-defs? ccic-term? defs)
;                    (evaluation-context? evalctx)
;                    (canonical-term? v defs))
; postcondition: (or (canonical-term? (refocus-aux evalctx v defs))
;                    (and (pair? (refocus-aux evalctx v defs))
;                         (evaluation-context? (car (refocus-aux evalctx v defs)))
;                         (ccic-term? (cdr (refocus-aux evalctx v defs)))))
(define (refocus-aux evalctx v defs)
  (trace-eval "***Auxilliary Refocusing***~n")
  (trace-eval "Canonical Term:~a~n" (pretty-format (unparse-term v (seteqv) #f)))
  (trace-eval "Context:~a~n" (pretty-format (unparse-evalctx evalctx)))
  (match* (evalctx v)
    [('() v)
     ;; evaluation done
     (iterate v defs)]

    ;; Plug v into the top frame of evalctx and choose to either:
    ;;
    ;; 1) Evaluate the plugged term as a potential principal redex using iterate
    ;;
    ;; 2) Evaluate subterms of the plugged term using refocus which can later be
    ;; potential principal redexes
    ;;
    ;; 3) Evaluate the surrounding context using refocus-aux if the plugged term
    ;; is not a potential redex but is a value.
    [((cons (FApp rand) evalctx) _)
     ;; case 1, try PROD-BETA
     (iterate `(,evalctx . ,(App v rand)) defs)]
    [((cons (FIndElim ind-name z orig-z P f orig-f branches) evalctx) v)
     ;; case 1, try IND-BETA
     (iterate `(,evalctx . ,(IndElim ind-name v z orig-z P f orig-f branches))
              defs)]

    [((cons (FUnk) evalctx) (Pi _ _ _ _))
     ;; case 1, try PROD-UNK
     (iterate `(,evalctx . ,(Unk v)) defs)]
    [((cons (FErr) evalctx) (Pi _ _ _ _))
     ;; case 1, try PROD-ERR
     (iterate `(,evalctx . ,(Err v)) defs)]
    [((cons (FUnk) evalctx) _)
     ;; case 3
     (refocus-aux evalctx (Unk v) defs)]
    [((cons (FErr) evalctx) _)
     ;; case 3
     (refocus-aux evalctx (Err v) defs)]

    [((cons (FLam x x-orig body) evalctx) _)
     ;; case 3
     (refocus-aux evalctx (Lam x x-orig v body) defs)]
    [((cons (FPi x x-orig body) evalctx) _)
     ;; case 3
     (refocus-aux evalctx (Pi x x-orig v body) defs)]
    [((cons
       (FConstrParam ind-name constr-name level rev-pre-params
                     (cons next-param later-params) args)
       evalctx)
      _)
     ;; case 2
     (refocus next-param
              (cons
               (FConstrParam ind-name constr-name level
                             (cons v rev-pre-params)
                             later-params args)
               evalctx))]
    [((cons
       (FConstrParam ind-name constr-name level rev-params '()
                     (cons first-arg rest-args))
       evalctx)
      _)
     ;; case 2
     (refocus first-arg
              (cons
               (FConstrArg ind-name constr-name level
                           (reverse (cons v rev-params))
                           '() rest-args)
               evalctx))]
    [((cons
       (FConstrParam ind-name constr-name level rev-params '() '())
       evalctx)
      _)
     ;; case 3
     (refocus-aux evalctx
                  (Constr ind-name constr-name level
                          (reverse (cons v rev-params)) '())
                  defs)]
    [((cons
       (FConstrArg ind-name constr-name level params
                   rev-pre-args (cons next-arg later-args))
       evalctx)
      _)
     ;; case 2
     (refocus next-arg
              (cons
               (FConstrArg ind-name constr-name level params
                           (cons v rev-pre-args) later-args)
               evalctx))]
    [((cons
       (FConstrArg ind-name constr-name level params rev-args '())
       evalctx)
      _)
     ;; case 3
     (refocus-aux evalctx
                  (Constr ind-name constr-name level params
                          (reverse (cons v rev-args)))
                  defs)]
    [((cons
       (FIndT name level rev-pre-args (cons next-arg later-args))
       evalctx)
      _)
     ;; case 2
     (refocus next-arg
              (cons
               (FIndT name level
                      (cons v rev-pre-args)
                      later-args)
               evalctx))]
    [((cons (FIndT name level rev-args '()) evalctx) _)
     ;; case 3
     (refocus-aux evalctx
                  (IndT name level
                        (reverse (cons v rev-args)))
                  defs)]

    [((cons (FCastSrc term target) evalctx) (Unk (Univ i)))
     ;; case 2
     (refocus term (cons (FCastTrm v target) evalctx) defs)]
    [((cons (FCastSrc term target) evalctx) (or (Univ _) (Pi _ _ _ _) (IndT _ _ _)))
     ;; case 2
     (refocus target (cons (FCastTrg term v) evalctx) defs)]
    [((cons (FCastSrc term target) evalctx) v)
     ;; case 1
     (iterate `(,evalctx . ,(Cast term v target)) defs)]
    [((cons (FCastTrg term source) evalctx) (or (Pi _ _ _ _) (IndT _ _ _)))
     ;; case 2
     (refocus term (cons (FCastTrm source v) evalctx) defs)]
    [((cons (FCastTrg term source) evalctx) v)
     ;; case 1
     (iterate `(,evalctx . ,(Cast term source v)) defs)]
    [((cons (FCastTrm source target) evalctx) v)
     ;; case 1
     (iterate `(,evalctx . ,(Cast v source target)) defs)]

    [(_ _) (error 'refocus-aux "Unexpected context:~n~a~nValue:~a~n"
                  (pretty-format (unparse-evalctx evalctx))
                  (pretty-format (unparse-term v (seteqv) #f)))]))

(define trace-eval? (make-parameter #f))
(define trace-eval
  (trace-if-param trace-eval?))

(define (~ t1 t2 defs [scope '()])
  (debug-log (format "Checking consistent conversion between ~a and ~a" t1 t2))
  ;; TODO: Ensure whether this is how the GCIC paper intended it to be implemented.
  (define canon-t1 (evaluate-subterms t1 defs))
  (define canon-t2 (evaluate-subterms t2 defs))
  (debug-log (format (string-append
                      "Consistent conversion check will proceed to check"
                      " α-consistency between canonical terms ~a and ~a")
                     canon-t1 canon-t2))
  (values (~α canon-t1 canon-t2 scope scope)
          canon-t1
          canon-t2))

;; Evaluates the arguments of head normal form terms. Useful for testing and
;; debugging.
(define (evaluate-subterms term defs)
  (match (evaluate term defs)
    [(cons evalctx t)
     (error 'evaluate-subterms
            "Stuck Evaluation.~nTerm:~n~a~nEvaluation context:~n~a~n"
            (unparse-term t defs #f)
            (unparse-evalctx evalctx))]
    ;; no evaluation under binders
    [(Lam x x-orig A t) (Lam x x-orig (evaluate-subterms A defs) t)]
    [(Pi x x-orig A B) (Pi x x-orig (evaluate-subterms A defs) B)]
    [(Univ i) term]
    [(Constr I c i as bs)
     (Constr I c i
             (map (λ (a) (evaluate-subterms a defs)) as)
             (map (λ (b) (evaluate-subterms b defs)) bs))]
    [(IndT I i as)
     (IndT I i (map (λ (a) (evaluate-subterms a defs)) as))]
    [(or (Unk (and t (IndT _ _ _))) (Err (and t (IndT _ _ _))))
     (Unk (evaluate-subterms t defs))]
    [(and t
          (or (Unk (or (Univ _) (Unk (Univ _)) (Err (Univ _))))
              (Err (or (Univ _) (Unk (Univ _)) (Err (Univ _))))))
     t]
    [(Cast term source (Unk (Univ level)))
     #:when (germ? source level)
     (Cast (evaluate-subterms term defs) source (Unk (Univ level)))]
    [c #:when (canonical-term? c) c]
    [c (error 'evaluate-subterms "Expected a canonical term, but got ~a" c)]))

#|
(require racket/trace)
(trace refocus refocus-aux iterate)
|#
