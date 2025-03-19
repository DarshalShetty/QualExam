#lang racket

(provide (all-defined-out))

(define variant (make-parameter #f))
(define supported-variants '(gcic-n gcic-g gcic-shift))

(define (set-variant variant^)
  (cond
    [(memv variant^ supported-variants) (variant variant^)]
    [else (error 'set-variant
                 "Variant '~a' not supported. Expected one of ~a"
                 variant^ supported-variants)]))

;; Terms used in bidirectional CIC, GCIC surface language and CastCIC
(define-struct Var (name) #:transparent)
(define-struct Univ (level) #:transparent)
(define-struct App (rator rand) #:transparent)
(define-struct Lam (fparam type body) #:transparent)
(define-struct Pi (fparam type body) #:transparent)
(define-struct IndT (name params) #:transparent)
(define-struct Constr (ind-name name params args) #:transparent)
(define-struct IndElim (ind-name scrut pred-fparam pred-body rec-name branches)
  #:transparent)
(define-struct branch (constr-name arg-names body))

;; Terms used only in GCIC surface language
(define-struct UnkSurf (level) #:transparent)

;; Terms used only in CastCIC
(define-struct Unk (type) #:transparent)
(define-struct Err (type) #:transparent)
(define-struct Cast (term source target) #:transparent)

(define-struct ind-def (name level param-types constrs) #:transparent)
(define-struct constr-def (name arg-types) #:transparent)

(define-struct Program (variant-name defs term) #:transparent)

(define (parse program)
  (match program
    [`((variant ,v) ,@defs ,term)
     (define defs^ (parse-defs defs))
     (define term^ (parse-term term defs^ (seteqv)))
     (Program v defs^ term^)]
    [_ (error 'parse-prog "Invalid program syntax: ~a" program)]))

(define (parse-defs defs)
  (for/fold ([res '()])
            ([def defs])
    (match-define `(data ,name ,level ,@params ,constrs) def)
    (when (dict-has-key? res name)
      (error 'parse-defs "Inductive type ~a has already been defined." name))
    (dict-set res name (parse-def name level params constrs res))))

(define (parse-def name level params constrs prev-defs)
  (define params^ (parse-telescope params prev-defs))
  (define tmp-ind-def (ind-def name level params^ #f))
  (define scope
    (for/seteqv ([index.type params^])
      (car index.type)))
  (define constrs^ (parse-constr-defs constrs name
                                      (dict-set prev-defs name tmp-ind-def)
                                      scope))
  (ind-def name level params^ constrs^))

;; A Telescope is an association list whose keys are identifiers and values are
;; types which refer to previous keys
(define (parse-telescope telescope prev-defs (scope (seteqv)))
  (match telescope
    ['() '()]
    [`((,var : ,type) . ,rest-telescope)
     #:when (symbol? var)
     (dict-set (parse-telescope rest-telescope prev-defs
                                (set-add scope var))
               var
               (parse-term type prev-defs scope))]
    [_ (error 'parse-telescope "Invalid telescope ~a" telescope)]))

(define (parse-constr-defs constrs ind-name prev-defs scope)
  (match constrs
    ['() (hasheqv)]
    [`((,name . ,arg-types) . ,rest-constrs)
     #:when (symbol? name)
     (define constructor-table (parse-constr-defs rest-constrs ind-name prev-defs scope))
     (when (dict-has-key? constructor-table name)
       (error 'parse-constr-defs "Constructor '~a' has already been defined in inductive type ~a" ind-name))
     (dict-set constructor-table name (parse-constr-def name arg-types prev-defs scope))]
    [_ (error 'parse-constr-defs "Invalid constructor definitions ~a" constrs)]))

(define (parse-constr-def name arg-types prev-defs scope)
  (constr-def name (parse-telescope arg-types prev-defs scope)))

(define (parse-term term defs scope)
  (define (recurse t) (parse-term t defs scope))
  (match term
    ;; GCIC-only term
    [`(? ,level) #:when (natural? level) (UnkSurf level)]

    ;; CastCIC-only terms
    [`(? ,type) (Unk (recurse type))]
    [`(err ,type) (Err (recurse type))]
    [`(< ,target <== ,source > ,t)
     (Cast (recurse t) (recurse source) (recurse target))]

    ;; Common terms
    [`(□ ,level) #:when (natural? level) (Univ level)]
    [y
     #:when (symbol? y)
     (cond
       [(set-member? scope y) (Var y)]
       [else (error 'parse-term "Free variable found: ~a" y)])]
    [`(λ (,x : ,T) ,body)
     #:when (symbol? x)
     (Lam x (recurse T) (parse-term body defs (set-add scope x)))]
    [`(Π (,x : ,T) ,body)
     #:when (symbol? x)
     (Pi x (recurse T) (parse-term body defs (set-add scope x)))]
    [`(@ ,ind-name ,constr-name ,@params & ,@args)
     #:when (and (symbol? ind-name) (symbol? constr-name))
     (cond
       [(not (dict-has-key? defs ind-name))
        (error 'parse-term
               (string-append
                "Constructor call ~a failed because ~a"
                " is not defined as an inductive type.")
               constr-name ind-name)]
       [(not (dict-has-key? (ind-def-constrs (dict-ref defs ind-name)) constr-name))
        (error 'parse-term
               (string-append
                "Constructor call ~a failed because it"
                " is not defined as in the inductive"
                " type definition for ~a.")
               constr-name ind-name)]
       [else
        (Constr ind-name constr-name (map recurse params) (map recurse args))])]
    [`(elim ,ind-name ,scrut as (λ (,z) ,P) rec ,f with . ,branches)
     #:when (and (symbol? z) (symbol? ind-name) (symbol? f))
     (unless (dict-has-key? defs ind-name)
       (error 'parse-term
               "Can not do elimination on inductve type ~a since it is not defined."
               ind-name))
     (unless (eqv? (length branches) (dict-count (ind-def-constrs (dict-ref defs ind-name))))
       (error 'parse-term
              (string-append
               "~a branches in inductive elimination doesn't match with the "
               "number of constructors in definition of inductive type '~a'")
              ind-name))
     (IndElim ind-name (recurse scrut) z
              (parse-term P defs (set-add scope z)) f
              (parse-elim-branches branches ind-name defs (set-add scope f)))]
    [`(,ind-name . ,params)
     #:when (dict-has-key? defs ind-name)
     (IndT ind-name (map recurse params))]
    [`(,rator ,rand)
     (App (recurse rator) (recurse rand))]
    [_
     (debug-log (format "def-names: ~a~n" (dict-keys defs)))
     (debug-log (format "scope: ~a~n" scope))
     (error 'parse-term "Invalid term syntax: ~a" term)]))

(define (parse-elim-branches branches ind-name defs scope)
  (match branches
    ['() '()]
    [`(((,constr-name . ,arg-names) => ,body) . ,rest-branches)
     #:when (for/and ([name `(,constr-name . ,arg-names)])
              (symbol? name))
     (unless (dict-has-key? (ind-def-constrs (dict-ref defs ind-name))
                            constr-name)
       (error 'parse-elim-branches
              "Invalid elimination branch because constructor ~a is not defined for ~a"
              constr-name ind-name))
     (define extended-scope
       (for/fold ([scope scope])
                 ([arg-name arg-names])
         (set-add scope arg-name)))
     (cons (branch constr-name arg-names
                   (parse-term body defs extended-scope))
           (parse-elim-branches rest-branches ind-name defs scope))]))

(define (unparse program)
  (match program
    [(Program variant-name defs term)
     `((variant ,variant-name)
       ,@(unparse-defs defs)
       ,(unparse-term term))]
    [_ (error 'unparse-prog "Invalid program: ~a" program)]))

(define (unparse-defs defs)
  (for/list ([def (dict-values defs)])
    (match-define (ind-def name level param-types constrs)
      def)
    (define-values (param-types^ scope)
      (unparse-telescope param-types (seteqv)))
    `(data ,name ,level ,param-types^ ,(unparse-constr-defs constrs scope))))


(define (unparse-constr-defs constrs scope)
  (for/list ([constr (dict-values constrs)])
    (match-define (constr-def name arg-types) constr)
    (define-values (arg-types^ _)
      (unparse-telescope arg-types scope))
    `(,name . ,arg-types^)))

(define (unparse-telescope telescope scope)
  (for/fold ([result '()]
             [scope scope])
            ([index/type telescope])
    (values
     (cons
      `(,(cdr index/type) : ,(unparse-term (cdr index/type) scope))
      result)
     (set-add scope (car index/type)))))

(define (unparse-term term [scope (seteqv)] [check-free? #t])
  (define (recurse t) (unparse-term t scope))
  (match term
    ;; GCIC-only term
    [(UnkSurf level) `(? ,level)]

    ;; CastCIC-only terms
    [(Unk type) `(? ,(recurse type))]
    [(Err type) `(err ,(recurse type))]
    [(Cast t source target)
     `(< ,(recurse target) <== ,(recurse source) > ,(recurse t))]

    ;; Common terms
    [(Univ level) `(□ ,level)]
    [(Var name)
     (cond
       [check-free?
        (cond
          [(set-member? scope name) name]
          [else (error 'unparse-term "Free variable found: ~a" name)])]
       [else name])]
    [(Lam x T body)
     `(λ (,x : ,(recurse T)) ,(unparse-term body (set-add scope x)))]
    [(Pi x T body)
     `(Π (,x : ,(recurse T)) ,(unparse-term body (set-add scope x)))]
    [(Constr ind-name constr-name params args)
     `(@ ,ind-name ,constr-name ,@(map recurse params) & ,@(map recurse args))]
    [(IndElim ind-name scrut z P f branches)
     `(elim ,ind-name ,(recurse scrut)
            as (λ (,z) ,(unparse-term P (set-add scope z)))
            rec ,f with .
            ,(unparse-elim-branches branches (set-add scope f)))]
    [(IndT name params) `(,name . ,(map recurse params))]
    [(App rator rand) `(,(recurse rator) ,(recurse rand))]
    [_ (error 'unparse-term "Invalid term: ~a" term)]))

(define (unparse-elim-branches branches scope)
  (for/list ([b branches])
    (match-define (branch constr-name arg-names body) b)
    (define extended-scope
      (for/fold ([scope^ scope])
                ([arg-name arg-names])
        (set-add scope^ arg-name)))
    `((,constr-name . ,arg-names) => ,(unparse-term body extended-scope))))

(define debug? (make-parameter #f))

;; Checks for valid syntax, free variables and globally unique variable binder names
(define (gcic-program? program)
  (*cic-program? gcic-term? program))

(define (ccic-program? program)
  (*cic-program? ccic-term? program))

(define (*cic-program? term? program)
  (match program
    [(Program variant-name defs term)
     (cond
       [(not (memv variant-name supported-variants))
        (debug-log (format "Unsupported GCIC variant: ~a" variant-name))
        #f]
       [(not (dict? defs))
        (debug-log (format "Defintion table in a program must be a dictionary, but found ~a" defs))
        #f]
       [(not (*cic-defs? term? defs))
        (debug-log (format "Program should have valid definitions, but found: ~a"
                           defs))
        #f]
       [(not (term? term defs (seteqv)))
        (debug-log (format "Program should end with a valid term, but found: ~a"
                           term))
        #f]
       [else #t])]
    [_
     (debug-log (format "Invalid GCIC program: ~a" program))
     #f]))

(define (*cic-defs? term? defs)
  (let/cc return
    (for/fold ([result #t]
               [prev-defs (hasheqv)]
               #:result result)
              ([d defs])
      (match-define `(,key-name . ,def) d)
      (match-define (ind-def name level param-types constrs)
        def)
      (cond
        [(not (symbol? name))
         (debug-log (format
                     (string-append  "Name of inductive type definition "
                                     "should be a symbol, but found: ~a")
                     name))
         (return #f)]
        [(not (natural? level))
         (debug-log (format
                     (string-append  "Level in definition of inductive type ~a"
                                     " should be a natural number, but found: ~a")
                     name level))
         (return #f)]
        [(not (eqv? key-name name))
         (debug-log (format
                     (string-append "Inductive type name in the definition table is "
                                    "'~a', but is '~a' in the definition itself.")
                     key-name name))
         (return #f)]
        [(dict-has-key? prev-defs name)
         (debug-log (format "Inductive type '~a' already defined." name))
         (return #f)]
        [else
         (define prev-defs^ (dict-set prev-defs name def))
         (cond
           [(not (*cic-telescope? term? param-types prev-defs^))
            (debug-log (format
                        (string-append
                         "Invalid parameter declaration in the "
                         "definition of inductive type ~a")
                        name))
            (return #f)]
           [(not (dict? constrs))
            (debug-log (format
                        (string-append
                         "Constructor definition table in inductive definition "
                         "should be a dictionary, but found ~a")
                        constrs))
            (return #f)]
           [(*cic-constr-defs? term? constrs prev-defs^
                               (list->seteqv (map car param-types)) name)
            (values #t prev-defs^)]
           [else
            (debug-log (format "Invalid inductive definition: ~a" def))
            (return #f)])]))))

(define (*cic-constr-defs? term? constrs prev-defs scope name)
  (for/and ([constr (dict-values constrs)]
            [key-name (dict-keys constrs)])
    (match-define (constr-def name arg-types) constr)
    (cond
      [(not (symbol? name))
       (debug-log (format
                   (string-append
                    "Name of constructor definition should be a symbol, "
                    "but found: ~a")
                   name))
       #f]
      [(not (eqv? key-name name))
       (debug-log (format
                   (string-append "Constructor name in the definition table is '~a'"
                                  ", but is '~a' in the definition itself.")
                   key-name name))
       #f]
      [(not (*cic-telescope? term? arg-types prev-defs scope))
       (debug-log (format (string-append
                           "Invalid argument declaration in the"
                           " definition of constructor: ~a")
                          name))
       #f]
      [else #t])))

(define (*cic-telescope? term? telescope defs [scope (seteqv)])
  (let/cc return
    (for/fold ([result #t]
               [scope scope]
               #:result result)
              ([index/type telescope])
      (match-define (cons index type) index/type)
      (cond
        [(not (symbol? index))
         (debug-log (format
                     "Index in a telescope should be a symbol, but found: ~a"
                     index))
         (return #f)]
        [(term? type defs scope) (values #t (set-add scope index))]
        [else
         (debug-log (format "Invalid telescope segment: ~a" index/type))
         (return #f)]))))

(define (gcic-term? term defs scope)
  (match term
    [(UnkSurf level)
     (cond
       [(not (natural? level))
        (debug-log (format "Level for unknown term (?) should be a natural number, but found: ~a"
                           level))
        #f]
       [else #t])]
    [_ (*cic-term? gcic-term? term defs scope)]))

(define (ccic-term? term defs scope)
  (match term
    [(or (Unk type) (Err type))
     (define-values (term-struct _) (struct-info term))
     (define-values (term-name _1 _2 _3 _4 _5 _6 _7) (struct-type-info term-struct))
     (cond
       [(not (ccic-term? type defs scope))
        (debug-log (format
                    "The type in a ~a term should be a valid term, but got: ~a"
                    term-name type))
        #f]
       [else #t])]
    [(Cast term source target)
     (define (recurse t) (ccic-term? t defs scope))
     (cond
       [(not (recurse term))
        (debug-log (format
                    "Term in cast should be a valid term, but found: ~a"
                    term))
        #f]
       [(not (recurse source))
        (debug-log (format
                    "Source type in cast should be a valid term, but found: ~a"
                    source))
        #f]
       [(not (recurse target))
        (debug-log (format
                    "Target type in cast should be a valid term, but found: ~a"
                    target))
        #f]
       [else #t])]
    [_ (*cic-term? ccic-term? term defs scope)]))

(define (*cic-term? self term defs scope)
  (define (recurse t) (self t defs scope))
  (match term
    [(Univ level)
     (cond
       [(not (natural? level))
        (debug-log (format "Level for universe term (□) should be a natural number, but found: ~a"
                           level))
        #f]
       [else #t])]
    [(Var name)
     (cond
       [(not (symbol? name))
        (debug-log (format "Variable name should be a symbol, but found: ~a" name))
        #f]
       [(not (set-member? scope name))
        (debug-log (format "Free variable found: ~a" term))
        #f]
       [else #t])]
    [(or (Lam x T body) (Pi x T body))
     (define-values (term-struct _) (struct-info term))
     (define-values (term-name _1 _2 _3 _4 _5 _6 _7) (struct-type-info term-struct))
     (cond
       [(not (symbol? x))
        (debug-log (format
                    (string-append
                     "The binder in ~a abstraction should be a symbol"
                     ", but found: ~a")
                    term-name x))
        #f]
       [(not (recurse T))
        (debug-log (format
                    (string-append "Type annotation in ~a abstraction "
                                   "should be a valid term, but found: ~a")
                    term-name T))
        #f]
       [(not (self body defs (set-add scope x)))
        (debug-log (format
                    (string-append
                     "The body in ~a abstraction should "
                     "be a valid term, but found: ~a")
                    term-name body))
        #f]
       [else #t])]
    [(Constr ind-name constr-name params args)
     (cond
       [(not (dict-has-key? defs ind-name))
        (debug-log (format
                    (string-append
                     "Inductive type name '~a' in instantiation of constructor "
                     "'~a' is not defined.")
                    ind-name constr-name))
        #f]
       [(not (dict-has-key? (ind-def-constrs (dict-ref defs ind-name)) constr-name))
        (debug-log (format
                    (string-append
                      "Instantiation of constructor '~a` failed because "
                      "it is not defined in the definition of inductive type '~a'")
                    constr-name ind-name))
        #f]
       [(not (for/and ([param params]) (recurse param)))
        (debug-log (format
                    "Invalid parameter in parameters of constructor instantiation: ~a"
                    params))
        #f]
       [(not (for/and ([arg args]) (recurse arg)))
        (debug-log (format
                    "Invalid argument in arguments of constructor instantiation: ~a"
                    args))
        #f]
       [else #t])]
    [(IndElim ind-name scrut z P f branches)
     (cond
       [(not (dict-has-key? defs ind-name))
        (debug-log (format
                    (string-append
                     "Inductive elimination failed because inductive type "
                     "'~a' is not defined.")
                    ind-name))
        #f]
       [(not (recurse scrut))
        (debug-log (format
                    (string-append
                     "Scrutinee of inductive elimination should be a valid term, "
                     "but found: ~a")
                    scrut))
        #f]
       [(not (symbol? z))
        (debug-log (format
                    (string-append
                     "Binder for motive in inductive elimination should be "
                     "a symbol, but found: ~a" )
                    z))
        #f]
       [(not (self P defs (set-add scope z)))
        (debug-log (format
                    (string-append
                     "Motive of inductive eliminator should be a valid "
                     "term, but found: ~a")
                    P))
        #f]
       [(not (symbol? f))
        (debug-log (format
                    (string-append
                     "Binder for recursive function in inductive elimination should be "
                     "a symbol, but found: ~a" )
                    f))
        #f]
       [(not (eqv? (length branches) (dict-count (ind-def-constrs (dict-ref defs ind-name)))))
        (debug-log (format
                    (string-append
                     "Inductive elimination has ~a branches which doesn't"
                     " match with the number of constructors in the definition "
                     "of inductive type '~a'.")
                    (length branches) ind-name))
        #f]
       [(not (*cic-elim-branches? self branches ind-name defs (set-add scope f)))
        (debug-log (format "Invalid branches in inductive eliminator. Found: ~a"
                           branches))
        #f]
       [else #t])]
    [(IndT name params)
     (cond
       [(not (dict-has-key? defs name))
        (debug-log (format
                    (string-append
                     "Inductive type instantiation failed because "
                     "'~a' is not defined.")
                    name))
        #f]
       [(not (for/and ([param params]) (recurse param)))
        (debug-log (format
                    (string-append
                     "Invalid parameter in parameters of inductive "
                     "type instantiation: ~a")
                    params))
        #f]
       [else #t])]
    [(App rator rand)
     (cond
       [(not (recurse rator))
        (debug-log (format
                    "Operator in application should be a valid term, but found: ~a"
                    rator))
        #f]
       [(not (recurse rand))
        (debug-log (format
                    "Operand in application should be a valid term, but found: ~a"
                    rand))
        #f]
       [else #t])]
    [_ (debug-log (format "Invalid term: ~a" term)) #f]))

(define (*cic-elim-branches? term? branches ind-name defs scope)
  (for/and ([b branches])
    (match-define (branch constr-name arg-names body) b)
    (cond
      [(not (dict-has-key? (ind-def-constrs (dict-ref defs ind-name)) constr-name))
       (debug-log (format "Constructor name '~a' not found in definition of inductive type '~a'"
                          constr-name ind-name))
       #f]
      [(not (term? body defs (set-union scope (list->seteqv arg-names))))
       (debug-log (format
                   "Body of inductive eliminator branch for constructor '~a' should be a valid term, but found: ~a"
                   constr-name body))
       #f]
      [else #t])))

;; Precondition: (and (ccic-term? t1) (ccic-term? t2))
(define (=α t1 t2 [scope1 '()] [scope2 '()])
  (match `(,t1 ,t2)
    [`(,(Cast term1 source1 target1) ,(Cast term2 source2 target2))
     #:when (and (=α term1 term2 scope1 scope2)
                 (=α source1 source2 scope1 scope2)
                 (=α target1 target2 scope1 scope2))
     #t]
    [`(,(Unk type1) ,(Unk type2))
     #:when (=α type1 type2 scope1 scope2)
     #t]
    [`(,(Err type1) ,(Err type2))
     #:when (=α type1 type2 scope1 scope2)
     #t]
    [_ (*α =α t1 t2 scope1 scope2)]))

;; Precondition: (and (ccic-term? t1) (ccic-term? t2))
(define (~α t1 t2 [scope1 '()] [scope2 '()])
  (match `(,t1 ,t2)
    [`(,(Cast term1 _ _) ,term2)
     #:when (~α term1 term2 scope1 scope2)
     #t]
    [`(,term1 ,(Cast term2 _ _))
     #:when (~α term1 term2 scope1 scope2)
     #t]
    [`(,(Unk _) ,_) #t]
    [`(,_ ,(Unk _)) #t]
    [_ (*α ~α t1 t2 scope1 scope2)]))

(define (*α self t1 t2 [scope1 '()] [scope2 '()])
  (match `(,t1 ,t2)
    [`(,(Univ level) ,(Univ level)) #t]
    [`(,(Var name1) ,(Var name2))
     #:when (eqv? (index-of scope1 name1) (index-of scope2 name2))
     #t]
    [`(,(Lam x1 T1 body1) ,(Lam x2 T2 body2))
     #:when (and
             (self T1 T2 scope1 scope2)
             (self body1 body2 (cons x1 scope1) (cons x2 scope2)))
     #t]
    [`(,(Pi x1 T1 body1) ,(Pi x2 T2 body2))
     #:when (and
             (self T1 T2 scope1 scope2)
             (self body1 body2 (cons x1 scope1) (cons x2 scope2)))
     #t]
    [`(,(IndT name params1) ,(IndT name params2))
     #:when (for/and ([param1 params1]
                      [param2 params2])
              (self param1 param2 scope1 scope2))
     #t]
    [`(,(Constr ind-name constr-name params1 args1)
       ,(Constr ind-name constr-name params2 args2))
     #:when (and (for/and ([param1 params1]
                           [param2 params2])
                   (self param1 param2 scope1 scope2))
                 (for/and ([arg1 args1]
                           [arg2 args2])
                   (self arg1 arg2 scope1 scope2)))
     #t]
    [`(,(IndElim ind-name scrut1 z1 P1 f1 branches1)
       ,(IndElim ind-name scrut2 z2 P2 f2 branches2))
     #:when (and (self scrut1 scrut2 scope1 scope2)
                 (self P1 P2 (cons z1 scope1) (cons z2 scope2))
                 (elim-branches-*α self branches1 branches2
                                   (cons f1 scope1) (cons f2 scope2)))
     #t]
    [`(,(App rator1 rand1) ,(App rator2 rand2))
     #:when (and (self rator1 rator2 scope1 scope2)
                 (self rand1 rand2 scope1 scope2))
     #t]
    [_ (debug-log (format "Not related:~n Term 1:~a~n Term 2:~a~n" t1 t2))
       #f]))

(define (elim-branches-*α term-*α? branches1 branches2 scope1 scope2)
  (for/and ([branch1 branches1]
            [branch2 branches2])
    (match `(,branch1 ,branch2)
      [`(,(branch constr-name arg-names1 body1)
         ,(branch constr-name arg-names2 body2))
       #:when (term-*α? body1 body2
                        (append arg-names1 scope1) (append arg-names2 scope2))
       #t]
      [_
       (debug-log (format "Branch not related:~n Branch 1:~a~n Branch 2:~a~n"
                          branch1 branch2))
       #f])))

(define (subst term for-symbol in-term)
  (define (recurse t) (subst term for-symbol t))
  (match in-term
    [(Univ level) in-term]
    [(Var name)
     (cond
       [(eqv? name for-symbol) term]
       [else (Var name)])]
    [(Lam y T body)
     (define-values (y^ body^)
       (subst-binder term for-symbol y body))
     (Lam y^ (recurse T) body^)]
    [(Pi y T body)
     (define-values (y^ body^)
       (subst-binder term for-symbol y body))
     (Pi y^ (recurse T) body^)]
    [(Constr ind-name constr-name params args)
     (Constr ind-name constr-name
             (for/list ([param params])
               (recurse param))
             (for/list ([arg args])
               (recurse arg)))]
    [(IndElim ind-name scrut z P f branches)
     (define-values (z^ P^)
       (subst-binder term for-symbol z P))
     (define-values (f^ branches^)
       (cond
         [(eqv? f for-symbol) (values f branches)]
         [else
          (define fresh-f (fresh-name f))
          (values
           fresh-f
           (subst-elim-branches term for-symbol
                                (subst-elim-branches (Var fresh-f)
                                                     f branch)))]))
     (IndElim ind-name (recurse scrut) z^ P^ f^ branches^)]
    [(App rator rand)
     (App (recurse rator) (recurse rand))]

    [(Cast term source target)
     (Cast (recurse term) (recurse source) (recurse target))]
    [(Unk type)
     (Unk (recurse type))]
    [(Err type)
     (Err (recurse type))]))

(define (subst-elim-branches term for-symbol in-branches)
  (for/list ([b in-branches])
    (match-define (branch constr-name arg-names body) b)
    (cond
      [(memv for-symbol arg-names) b]
      [else
       (define-values (arg-names^ body^)
         (for/fold ([arg-names^ '()]
                    [body^ body]
                    #:result (subst term for-symbol body))
                   ([arg-name arg-names])
           (define fresh-arg-name (fresh-name arg-name))
           (values (append arg-names^ `(,fresh-arg-name))
                   ;; This can be optimized by using parallel substitution
                   (subst (Var fresh-arg-name) arg-name body^))))
       (branch constr-name arg-names^ body^)])))

(define (subst-binder term for-symbol bind-name in-term)
  (cond
    [(eqv? bind-name for-symbol) (values bind-name in-term)]
    [else
     (define fresh-bind-name (fresh-name bind-name))
     (values
      fresh-bind-name
      (subst term for-symbol
             (subst (Var fresh-bind-name)
                    bind-name in-term)))]))

(define (fresh-name name)
  (gensym (string->symbol (string-append (symbol->string name) "§"))))

(define (debug-log message)
  (when (debug?)
      (printf "~a~n" message)))
