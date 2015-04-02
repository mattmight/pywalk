(module pywalk racket/base
  
  ; A module for walking over and transforming python ASTs.
  
  (provide (all-defined-out))
  
  (require racket/set)
  (require racket/match)
  (require racket/function)
    
  ;; Dynamically scope parameters accessible during transformation:
  
  (define loop-scope (make-parameter 'none)) ; may be: 'for 'while 'none
  (define var-scope (make-parameter 'global)) ; may be: 'global 'def 'class 
  (define local-vars (make-parameter (set))) ; set of vars defined locally in this scope
  
  
  ;; Auxiliary functions
  
  ;;; Generate a temporary name:
  (define tmp-index 0)
  
  (define (tmp)
    (set! tmp-index (+ 1 tmp-index))
    (string->symbol (format "_tmp_~a" tmp-index)))
  
  (define (tmp-name)
    `(Name ,(tmp)))
  
  ;;; Call a function with positional args:
  (define (call fun args)
    `(Call (func ,fun)
           (args . ,args)
           (keywords)
           (starargs #f)
           (kwargs #f)))
  
  (define (assign var expr)
    `(Assign (targets ,var) (value ,expr)))
  
  ;; Transformations
  
  ; walk-module : module -> module
  (define (walk-module module
                       #:transform-stmt    [transform-stmt #f] 
                       #:transform-stmt/bu [transform-stmt/bu #f]
                       #:transform-expr    [transform-expr #f]
                       #:transform-expr/bu [transform-expr/bu #f])
    
    ; walk-stmts : stmt* -> stmt*
    (define (walk-stmts stmts)
      
      (define (recur stmts)
        (match stmts
          [(cons (and head `(Local . ,vars)) tail)
           ; =>
           (parameterize ([local-vars (list->set vars)])
             (cons (walk-stmt head)
                   (recur tail)))]
          
          [(cons head tail)
           ; =>
           (cons (walk-stmt head)
                 (recur tail))]
          
          ['()
           '()]
          
          [else (error (format "could not `recur` on: ~s" stmts))]))
      
      (apply append (recur stmts)))
    
    
    ; walk-stmt : stmt -> stmt*
    (define (walk-stmt stmt)
      
      (define stmts (if transform-stmt
                        (transform-stmt stmt)
                        (list stmt)))
      
      (walk*-stmts stmts))
    
    ; walk*-stmts : stmt* -> stmt*
    (define (walk*-stmts stmts)
      (apply append (map walk*-stmt stmts)))
    
    
    ; walk*-stmt : stmt -> stmt*
    (define (walk*-stmt stmt)
      
      (define prepended-stmts '())
      (define appended-stmts '())
      
      (define prepend-stmt!
        (λ (stmt)
          (set! prepended-stmts (append prepended-stmts (list stmt)))))
      
      (define append-stmt!
        (λ (stmt)
          (set! appended-stmts (append appended-stmts (list stmt)))))
      
      
      ; Only walk-stmt knows when it's safe to call these:
      (define (walk-expr! expr)
        (walk-expr expr prepend-stmt! append-stmt!))
      
      (define (walk-exprs! exprs)
        (map walk-expr! exprs))
      
      ; walk-keywords! : list[keyword] -> list[keyword]
      (define (walk-keywords! keywords)
        (map (λ (keyword)
               (match keyword
                 [`(,id ,value)  `(,id ,(walk-expr! value))]))
             keywords))
      
      ; walk-expr : expr? -> expr?
      (define (walk-expr expr [prepend! #f] [append! #f])
        
        ; walk-expr should use these instead of walk-expr[s]!:
        (define (walk-expr$ expr)
          (walk-expr expr prepend! append!))
        
        (define (walk-exprs$ exprs)
          (map walk-expr$ exprs))
        
        (define (walk-comprehension comp)
          (match comp
            [`(for ,target in ,iter if . ,conds)
             `(for ,(walk-expr target)
                in ,(walk-expr iter)
                if ,@(map walk-expr conds))]
            
            [else (error (format "malformed compreshension: ~s" comp))]))
        
        (define (walk-comprehension$ comp)
          (match comp
            [`(for ,target in ,iter if . ,conds)
             `(for ,(walk-expr target)
                in ,(walk-expr$ iter)
                if ,@(map walk-expr conds))]
            
            [else (error (format "malformed comprehension: ~s" comp))]))
        
        
        ; walk-slice$ : slice -> slice
        (define (walk-slice$ slice)
          (match slice
            [`(Index ,expr)
             `(Index ,(walk-expr$ expr))]
            
            [`(Slice ,lo? ,hi? ,step?)
             `(Slice ,(walk-expr$ lo?)
                     ,(walk-expr$ hi?)
                     ,(walk-expr$ step?))]
            
            [`(ExtSlice . ,slices)
             `(ExtSlice . ,(map walk-slice$ slices))]
            
            [else (error (format "can't walk slice: ~s" slice))]))
        
        ; walk-keywords$ : list[keyword] -> list[keyword]
        (define (walk-keywords$ keywords)
          (map (λ (keyword)
                 (match keyword
                   [`(,id ,value)  `(,id ,(walk-expr$ value))]))
               keywords))
        
        ; walk-arguments$ : arguments -> arguments
        (define (walk-arguments$ args)
          (match args
            [`(Arguments
               (args . ,ids)
               (arg-types . ,arg-types) 
               (vararg ,vararg . ,vararg-type) 
               (kwonlyargs . ,kwonlyargs) 
               (kwonlyarg-types . ,kwonlyarg-types)
               (kw_defaults . ,kw_defaults)
               (kwarg ,kwarg . ,kwarg-type)
               (defaults . ,defaults))
             
             `(Arguments
               (args . ,ids)
               (arg-types . ,(walk-exprs$ arg-types))
               (vararg ,vararg . ,(walk-exprs$ vararg-type))
               (kwonlyargs . ,kwonlyargs) 
               (kwonlyarg-types . ,(walk-exprs$ kwonlyarg-types))
               (kw_defaults . ,(walk-exprs$ kw_defaults))
               (kwarg ,kwarg . ,(walk-exprs$ kwarg-type))
               (defaults . ,(walk-exprs$ defaults)))]
          
            [else (error (format "can't walk arguments: ~s" args))]))
        
        (when (and transform-expr expr)
          (set! expr (transform-expr expr prepend! append!)))
        
        (define 
          expr+
          
          (match expr
            [#f #f]
            
            ; (BoolOp <boolop> <expr>*)
            [`(BoolOp ,op ,first . ,rest)
             `(BoolOp ,op ,(walk-expr$ first) . ,(walk-exprs rest))]
            
            ; (BinOp <expr> <operator> <expr>)
            [`(BinOp ,lhs ,op ,rhs)
             ; TODO/BUG: Fix for proper order of eval in Python
             `(BinOp ,(walk-expr$ lhs) ,op ,(walk-expr$ rhs))]
            
            ; (UnaryOp <unaryop> <expr>)
            [`(UnaryOp ,op ,expr)
             `(UnaryOp ,op ,(walk-expr$ expr))]
            
            ; (Lambda <arguments> <expr>)
            [`(Lambda ,args ,expr)
             `(Lambda ,(walk-arguments$ args) ,(walk-expr expr))]
            
            ; (IfExp <expr> <expr> <expr>)
            [`(IfExp ,cond ,then ,else)
             `(IfExp ,(walk-expr$ cond)
                     ,(walk-expr then)
                     ,(walk-expr else))]
            
            ; (Dict (keys <expr>*) (values <expr>*))
            [`(Dict (keys . ,keys) (values . ,values))
             `(Dict (keys ,@(walk-exprs$ keys))
                    (values ,@(walk-exprs$ values)))]
            
            ; (Set <expr>*)
            [`(Set . ,exprs)
             `(Set ,@(walk-exprs$ exprs))]
            
            ; (ListComp <expr> <comprehension>*)
            [`(ListComp ,expr ,comp1 . ,comps)
             `(ListComp ,(walk-expr expr) 
                        ,(walk-comprehension$ comp1)
                        ,@(map walk-comprehension comps))]
            
            
            ; (SetComp <expr> <comprehension>*)
            [`(SetComp ,expr ,comp1 . ,comps)
             `(SetComp ,(walk-expr expr) 
                       ,(walk-comprehension$ comp1)
                       ,@(map walk-comprehension comps))]
            
            ; (DictComp <expr> <expr> <comprehension>*)
            [`(DictComp ,key ,value ,comp1 . ,comps)
             `(DictComp ,(walk-expr key) ,(walk-expr value)
                        ,(walk-comprehension$ comp1) 
                        ,@(map walk-comprehension comps))]
            
            ; (GeneratorExp <expr> <comprehension>*)
            [`(GeneratorExp ,expr ,comp1 . ,comps)
             `(GeneratorExp ,(walk-expr expr)
                            ,(walk-comprehension$ comp1)
                            ,@(map walk-comprehension comps))]
            
            ; (Yield)
            [`(Yield)
             '(Yield)]
            
            ; (Yield <expr>)
            [`(Yield ,expr)
             `(Yield ,(walk-expr$ expr))]
            
            ; (YieldFrom <expr>)
            [`(YieldFrom ,expr)
             `(YieldFrom ,(walk-expr$ expr))]
            
            ; (Compare (left        <expr>) 
            ;          (ops         <cmpop>*)
            ;          (comparators <expr>*))
            [`(Compare (left ,left)
                       (ops . ,ops)
                       (comparators ,comp1 . ,comparators))
             `(Compare (left ,(walk-expr$ left))
                       (ops ,@ops)
                       (comparators ,(walk-expr$ comp1) ,@(walk-exprs comparators)))]
            
            
            ; (Call (func <expr>)
            ;       (args <expr>*)
            ;       (keywords <keyword>*)
            ;       (starargs <expr?>)
            ;       (kwargs <expr?>))
            [`(Call (func ,expr)
                    (args . ,args)
                    (keywords . ,keywords)
                    (starargs ,starargs)
                    (kwargs ,kwargs))
             `(Call (func ,(walk-expr$ expr))
                    (args . ,(walk-exprs$ args))
                    (keywords . ,(walk-keywords$ keywords))
                    (starargs ,(walk-expr$ starargs))
                    (kwargs ,(walk-expr$ kwargs)))]
            
            ; (Num <number>)
            [`(Num ,n)   expr]
            
            ; (Str <string>)
            [`(Str ,str) expr]
            
            ; (Bytes <byte-string>)
            [`(Bytes ,bytes) expr]
            
            ; (NameConstant <name-constant>)
            [`(NameConstant ,const)
             `(NameConstant ,const)]
            
            ; (Ellipsis)
            [`(Ellipsis)
             '(Ellipsis)]
            
            ; (Attribute <expr> <identifier>)
            [`(Attribute ,expr ,id)
             `(Attribute ,(walk-expr$ expr) ,id)]
            
            ; (Subscript <expr> <slice>)
            [`(Subscript ,expr ,slice)
             `(Subscript ,(walk-expr$ expr) 
                         ,(walk-slice$ slice))]
            
            ; (Starred <expr>)
            [`(Starred ,expr)
             `(Starred ,(walk-expr$ expr))]
            
            ; (Name <identifier>)
            [`(Name ,id) 
             `(Name ,id)]
            
            ; (List <expr>*)
            [`(List . ,exprs)
             `(List ,@(walk-exprs$ exprs))]
            
            ; (Tuple <expr>*)
            [`(Tuple . ,exprs)
             `(Tuple ,@(walk-exprs$ exprs))]
            
            [else (error (format "don't know how to walk-expr: ~s" expr))]))
        
        (if (and transform-expr/bu expr+)
            (transform-expr/bu expr+ prepend! append!)
            expr+))    
      
      
      ; walk-exprs : list[expr] -> list[expr]
      (define (walk-exprs exprs) (map walk-expr exprs))
      
      ; walk-keywords : list[keyword] -> list[keyword]
      (define (walk-keywords keywords [prepend! #f] [append! #f])
        (map (λ (keyword)
               (match keyword
                 [`(,id ,value)  `(,id ,(walk-expr value prepend! append!))]))
             keywords))
      
      
      ; walk-arguments : arguments -> arguments
      (define (walk-arguments args [prepend! #f] [append! #f])
        (match args
          [`(Arguments
             (args . ,ids)
             (arg-types . ,arg-types) 
             (vararg ,vararg . ,vararg-type) 
             (kwonlyargs . ,kwonlyargs) 
             (kwonlyarg-types . ,kwonlyarg-types)
             (kw_defaults . ,kw_defaults)
             (kwarg ,kwarg . ,kwarg-type)
             (defaults . ,defaults))
           
           `(Arguments
             (args . ,ids)
             (arg-types . ,(walk-exprs arg-types))
             (vararg ,vararg . ,(walk-exprs vararg-type))
             (kwonlyargs . ,kwonlyargs) 
             (kwonlyarg-types . ,(walk-exprs kwonlyarg-types))
             (kw_defaults . ,(walk-exprs kw_defaults))
             (kwarg ,kwarg . ,(walk-exprs kwarg-type))
             (defaults . ,(walk-exprs defaults)))]
          
          [else (error (format "can't walk arguments: ~s" args))]))
      
      
      ; walk-withitem : withitem -> withitem
      (define (walk-withitem withitem)
        (match withitem
          [`(,ctxt #f)     `(,(walk-expr ctxt) #f)]
          [`(,ctxt ,id)    `(,(walk-expr ctxt) ,id)]))
      
      
      ; walk-handlers : list[excepthandler] -> list[excepthandler]
      (define (walk-handlers handlers)
        (for/list ([handler handlers])
          (match handler
            [`(except #f #f . ,body)
             `(except #f #f ,@(walk-stmts body))]
            
            [`(except ,exn #f . ,body)
             `(except ,(walk-expr exn) #f ,@(walk-stmts body))]
            
            [`(except ,exn ,id . ,body)
             `(except ,(walk-expr exn) ,id ,@(walk-stmts body))]
            
            [else (error "can't walk handler: ~s" handler)])))
      
      (define transformed 
        (match stmt
          
          ; (FunctionDef
          ;   (name <identifier>)
          ;   (args <arguments>)
          ;   (body <stmt>*)
          ;   (decorator_list <expr>*)
          ;   (returns <expr?>))
          [`(FunctionDef 
             (name ,name)
             (args ,args)
             (body . ,body)
             (decorator_list . ,decorators)
             (returns ,returns))
           
           (list `(FunctionDef 
                   (name ,name)
                   (args ,(walk-arguments args))
                   (body . ,(parameterize ([loop-scope 'none]
                                           [var-scope  'def])
                              (walk-stmts body)))
                   (decorator_list . ,(map walk-expr decorators))
                   (returns ,(walk-expr! returns))))]
          
          ; (ClassDef
          ;   (name <identifier>)
          ;   (bases <expr>*)
          ;   (keywords <keyword>*)
          ;   (starargs <expr?>)
          ;   (kwargs <expr?>)
          ;   (body <stmt>*)
          ;   (decorator_list <expr>*))
          [`(ClassDef
             (name ,id)
             (bases . ,bases)
             (keywords . ,keywords)
             (starargs ,starargs)
             (kwargs ,kwargs)
             (body . ,body)
             (decorator_list . ,decorators))
           (list 
            `(ClassDef
              (name ,id)
              (bases ,@(walk-exprs! bases))
              (keywords ,@(walk-keywords! keywords))
              (starargs ,(walk-expr! starargs))
              (kwargs ,(walk-expr! kwargs))
              (body . ,(parameterize ([loop-scope 'none]
                                      [var-scope 'class])
                         (walk-stmts body)))
              (decorator_list ,@(walk-exprs decorators))))]
          
          ; (Return <expr>?)
          [`(Return)
           (list '(Return))]
          
          [`(Return ,expr)
           (list `(Return ,(walk-expr! expr)))]
          
          
          ; (Delete <expr>*)
          [`(Delete . ,exprs)
           (list `(Delete ,@(map walk-expr exprs)))]
          
          ; (Assign (targets <expr>*) (value <expr>))
          [`(Assign (targets . ,targets) (value ,value))
           (list `(Assign (targets . ,(map walk-expr targets)) 
                          (value ,(walk-expr value))))]
          
          ; (AugAssign <expr> <operator> <expr>)
          [`(AugAssign ,lhs ,op ,rhs)
           (list `(AugAssign ,(walk-expr lhs) ,op ,(walk-expr! rhs)))]
          
          ; (For (target <expr>) (iter <expr>) (body <stmt>*) (orelse <stmt>*))
          [`(For (target ,target) (iter ,iter) (body . ,body) (orelse . ,orelse))
           (list `(For (target ,(walk-expr target))
                       (iter ,(walk-expr iter))
                       (body ,@(parameterize ([loop-scope 'for])
                                 (walk-stmts body)))
                       (orelse ,@(walk-stmts orelse))))]
          
          ; (While (test <expr>) (body <stmt>*) (orelse <stmt>*))
          [`(While (test ,test) (body . ,body) (orelse . ,orelse))
           (list `(While (test ,(walk-expr test))
                         (body ,@(parameterize ([loop-scope 'while])
                                   (walk-stmts body)))
                         (orelse ,@(walk-stmts orelse))))]
          
          ; (If (test <expr>) (body <stmt>*) (orelse <stmt>*))
          [`(If (test ,test) (body . ,body) (orelse . ,orelse))
           (list `(If (test ,(walk-expr test))
                      (body ,@(walk-stmts body))
                      (orelse ,@(walk-stmts orelse))))]
          
          
          ; (With [<withitem>*] <stmt>*)
          [`(With ,withitems . ,body)
           (list `(With ,(map walk-withitem withitems) 
                        ,@(walk-stmts body)))]
          
          ; (Raise) 
          [`(Raise)
           (list '(Raise))]
          
          ; (Raise <expr>)
          [`(Raise ,expr)
           (list `(Raise ,(walk-expr expr)))]
          
          ; (Raise <expr> <expr>)
          [`(Raise ,exn ,msg)
           (list `(Raise ,(walk-expr exn) ,(walk-expr msg)))]
          
          ; (Try (body <stmt>*)
          ;      (handlers <excepthandler>*)
          ;      (orelse <stmt>*)
          ;      (finalbody <stmt>*))
          [`(Try (body . ,body)
                 (handlers . ,handlers)
                 (orelse . ,orelse)
                 (finalbody . ,finalbody))
           (list 
            `(Try (body ,@(walk-stmts body))
                  (handlers ,@(walk-handlers handlers))
                  (orelse ,@(walk-stmts orelse))
                  (finalbody ,@(walk-stmts finalbody))))]
          
          ; (Assert <expr>)  
          [`(Assert ,expr)
           (list `(Assert ,(walk-expr! expr)))]
          
          ; (Assert <expr> <expr>)
          [`(Assert ,test ,msg)
           (list `(Assert ,(walk-expr! test) ,(walk-expr msg)))]
          
          ; (Import <alias>*)
          [`(Import . ,aliases)
           (list `(Import . ,aliases))]
          
          ; (ImportFrom (module <identifier?>)
          ;             (names <alias>*)
          ;             (level <int?>))
          [`(ImportFrom (module . ,module)
                        (names . ,names)
                        (level . ,level))
           
           (list `(ImportFrom (module . ,module)
                              (names . ,names)
                              (level . ,level)))]
          
          ; (Global <identifier>+)
          [`(Global . ,ids)
           (list `(Global ,@ids))]
          
          ; (Nonlocal <identifier>+)
          [`(Nonlocal . ,ids)
           (list `(Nonlocal ,@ids))]
          
          ; (Expr <expr>)
          [`(Expr ,expr)
           (list `(Expr ,(walk-expr! expr)))]
          
          ; (Pass) 
          [`(Pass)
           (list '(Pass))]
          
          ; (Break)
          [`(Break)
           (list '(Break))]
          
          ; (Continue)
          [`(Continue)
           (list '(Continue))]
          
          ; Synthetic statements:
          [`(Local . ,ids)
           (list `(Local . ,ids))]
          
          [`(Comment ,string)
           (list `(Comment ,string))]
          
          [else (error (format "can't walk stmt: ~s" stmt))]))
      
      (define transformed+ (append prepended-stmts transformed appended-stmts))
      
      (if (not transform-stmt/bu)
          transformed+
          (apply append (map transform-stmt/bu transformed+))))

          
          
    
    (match module
      [`(Module . ,stmts)
       `(Module ,@(apply append (map walk-stmt stmts)))]))
  
  
  
  
  
  (define (walk/fix prog
                    #:transform-expr [transform-expr #f]
                    #:transform-expr/bu [transform-expr/bu #f]
                    #:transform-stmt [transform-stmt #f]
                    #:transform-stmt/bu [transform-stmt/bu #f]
                    #:trace-debug [trace-debug? #f]) 
    (when trace-debug?
      (write prog))
    
    (let ([prog* (walk-module prog 
                              #:transform-expr transform-expr
                              #:transform-stmt transform-stmt
                              #:transform-expr/bu transform-expr/bu
                              #:transform-stmt/bu transform-stmt/bu)])
      (if (equal? prog* prog)
          prog
          (walk/fix prog*
                    #:transform-expr transform-expr
                    #:transform-stmt transform-stmt
                    #:transform-expr/bu transform-expr/bu
                    #:transform-stmt/bu transform-stmt/bu
                    #:trace-debug trace-debug?))))
  
  
  (define (locally-assigned stmts)
    (cond
      [(null? stmts)  (set)]
      [else
       (define stmt (car stmts))
       (define rest (cdr stmts))
       
       (define assigned-in-rest (locally-assigned rest))
       
       (define (targets-in target-expr)
         (match target-expr
           [`(Name ,name)               (set name)]
           [`(Starred ,target)          (targets-in target)]
           [`(Tuple . ,targets)         (apply set-union (map targets-in targets))]
           [`(List . ,targets)          (apply set-union (map targets-in targets))]
           [`(Attribute ,_ ,_)          (set)]
           [`(Subscript ,_ ,_)          (set)]
           
           [else (error (format "can't find targets in ~s" target-expr))]))
       
       (match stmt
         [`(FunctionDef
            (name ,name) 
            . ,_)
          
          (set-add assigned-in-rest name)]
         
         [`(ClassDef
            (name ,name)
            . ,_)
          
          (set-add assigned-in-rest name)]
         
         [`(Return . ,_) 
          assigned-in-rest]
         
         [`(Delete . ,_)
          assigned-in-rest]
         
         [`(Assign (targets . ,targets) (value ,_))
          (set-union
           assigned-in-rest
           (apply set-union (map targets-in targets)))]
         
         [`(AugAssign ,_ ,_ ,_)
          ; AugAssign can't declare variables (technically)
          assigned-in-rest]
         
         [`(For (target ,target)
                (iter ,iter) 
                (body . ,body)
                (orelse . ,orelse))
          (set-union
           assigned-in-rest
           (targets-in target)
           (locally-assigned body) 
           (locally-assigned orelse))]
         
         [`(While (test ,test) (body . ,body) (orelse . ,orelse))
          (set-union
           assigned-in-rest
           (locally-assigned body)
           (locally-assigned orelse))]
         
         [`(If (test ,expr) (body . ,body) (orelse . ,orelse))
          (set-union 
           assigned-in-rest
           (locally-assigned body)
           (locally-assigned orelse))]
         
         [`(With [(,exprs ,names) ...] . ,body)
          (set-union 
           assigned-in-rest
           (for/set ([n names] #:when n) n)
           (locally-assigned body))]
         
         [`(Raise . ,_)
          assigned-in-rest]
         
         [`(Try (body . ,body)
                (handlers [except ,exns ,names . ,bodies] ...)
                (orelse . ,orelse)
                (finalbody . ,finalbody))
          (set-union
           assigned-in-rest
           (locally-assigned body)
           (locally-assigned orelse)
           (locally-assigned finalbody)
           (apply set (filter identity names)))]
         
         [`(Assert . ,_)
          assigned-in-rest]
         
         [`(Import . ,_)
          assigned-in-rest]
         
         [`(ImportFrom . ,_)
          assigned-in-rest]
         
         [`(,(or 'Global 'Nonlocal) . ,names)
          (set-subtract assigned-in-rest (apply set names))]
         
         [`(Expr ,expr)
          assigned-in-rest]
         
         [`(Pass) 
          assigned-in-rest]
         
         [`(Break)
          assigned-in-rest]
         
         [`(Continue)
          assigned-in-rest]
         
         
         ; Synthetics:
         [`(Comment . ,_)
          assigned-in-rest]
         
         [`(Local . ,_)
          assigned-in-rest]
         
         [else (error (format "unknown statement: ~s" stmt))])]))
  
  )


