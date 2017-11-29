#lang plai-typed


; Basic expressions
(define-type ExprC
  [numC  (n : number)]
  [idC   (s : symbol)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [methodC (name : symbol) (arg : symbol) (body : ExprC)]
  ;[appC  (fun : ExprC) (arg : ExprC)]
  [ifC   (c : ExprC) (y : ExprC) (n : ExprC)]
  [seqC  (e1 : ExprC) (e2 : ExprC)]
  [setC  (var : symbol) (arg : ExprC)]
  [letC  (name : symbol) (arg : ExprC) (body : ExprC)]
  [classC (pai : symbol) (var : symbol) (m1 : ExprC) (m2 : ExprC)]
  [newC   (name : symbol) (val : ExprC)]
  [sendC  (obj : ExprC) (metName : symbol) (arg : ExprC)]
  )


; Sugared expressions
(define-type ExprS
  [numS    (n : number)]
  [idS     (s : symbol)]
  [methodS (name : symbol) (arg : symbol) (body : ExprS)]
  ;[appS    (fun : ExprS) (arg : ExprS)]
  [plusS   (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [multS   (l : ExprS) (r : ExprS)]
  [ifS     (c : ExprS) (y : ExprS) (n : ExprS)]
  [seqS    (e1 : ExprS) (e2 : ExprS)]
  [setS    (var : symbol) (arg : ExprS)]
  [letS    (name : symbol) (arg : ExprS) (body : ExprS)]
  [classS  (pai : symbol) (var : symbol) (m1 : ExprS) (m2 : ExprS)]
  [newS    (name : symbol) (val : ExprS)]
  [sendS   (obj : ExprS) (metName : symbol) (arg : ExprS)]
  )


; Removing the sugar
(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS    (n)        (numC n)]
    [idS     (s)        (idC s)]
    [methodS (name arg body)    (methodC name arg (desugar body))]
    ;[appS    (fun arg)  (appC (desugar fun) (desugar arg))]
    [plusS   (l r)      (plusC (desugar l) (desugar r))]
    [multS   (l r)      (multC (desugar l) (desugar r))]
    [bminusS (l r)      (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS (e)        (multC (numC -1) (desugar e))]
    [ifS     (c s n)    (ifC (desugar c) (desugar s) (desugar n))]
    [seqS    (e1 e2)    (seqC (desugar e1) (desugar e2))]
    [setS    (var expr) (setC  var (desugar expr))]
    [letS    (n a b)    (letC n (desugar a) (desugar b))]
    [classS  (pai var m1 m2) (classC pai var (desugar m1) (desugar m2))]    
    [newS    (name val) (newC name (desugar val))]
    [sendS   (obj metName arg) (sendC (desugar obj) metName (desugar arg))]
    ))


; We need a new value for the box
(define-type Value
  [numV  (n : number)]
  ;[closV (arg : symbol) (body : ExprC) (env : Env)]
  [classV (pai : symbol) (var : symbol) (m1 : Value) (m2 : Value)]
  [methodV (name : symbol) (arg : symbol) (body : ExprC)]
  [objectV (var : Binding) (classe : symbol) (pai : Value)]
  )


; Bindings associate symbol with location
(define-type Binding
        [bind (name : symbol) (val : (boxof Value))])

; Env remains the same, we only change the Binding
(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)
(define Object (classV 'Object 'a (methodV 'notAMethod1 'a (numC 1984)) (methodV 'notAMethod2 'b (numC 42))))

(define-type Result
        [res (met : Value) (env : Env)])

; Find the name of a variable
(define (lookup [for : symbol] [env : Env]) : (boxof Value)
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string for) " was not found"))] ; variable is undefined
            [else (cond
                  [(symbol=? for (bind-name (first env)))   ; found it!
                                 (bind-val (first env))]
                  [else (lookup for (rest env))])]))        ; check in the rest

; Create object recursivelly
(define (createObject [classe : symbol] [val : Value] [env : Env]) : Value
  (let ([CLASS (unbox (lookup classe env))])
    (cond
      [(equal? classe 'Object) (objectV (bind 'notAVariable (box (numV 0))) 'Object (numV 0))]
      [else
       (objectV (bind (classV-var CLASS) (box val)) classe (createObject (classV-pai CLASS) (numV 0) env))]
    )))

; Build instace variables from obj
(define (buildEnv [obj : Value] [env : Env]) : Env
  (cond
    [(equal? (objectV-classe obj) 'Object) env]
    [else
     (cons (objectV-var obj) (buildEnv (objectV-pai obj) env))]
    ))

; Find method and assemble environment
(define (findMethod [initial : Value] [obj : Value] [name : symbol] [arg : Value] [env : Env]) : Result
  (let* ([CLASS (unbox (lookup (objectV-classe obj) env))]
         [M1 (classV-m1 CLASS)]
         [M2 (classV-m2 CLASS)])
    (cond
      [(equal? (methodV-name M1) name)
        (let ([selfBind (bind 'self (box initial))]
              [paraBind (bind (methodV-arg M1) (box arg))]) 
          (res (classV-m1 CLASS) 
                           (extend-env selfBind (extend-env paraBind (buildEnv obj env)))))]
      [(equal? (methodV-name M2) name)
        (let ([selfBind (bind 'self (box initial))]
              [paraBind (bind (methodV-arg M2) (box arg))]) 
          (res (classV-m2 CLASS) 
                           (extend-env selfBind (extend-env paraBind (buildEnv obj env)))))]
      [(equal? (objectV-classe obj) 'Object)
       (error 'send (string-append "Class does not respond to the method " (symbol->string name)))]
      [else
       (findMethod initial (objectV-pai obj) name arg env)]
      )
    ))

; Auxiliary operators
(define (num+ [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (+ (numV-n l) (numV-n r)))]
        [else
             (error 'num+ "One of the arguments is not a number")]))

(define (num* [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (* (numV-n l) (numV-n r)))]
        [else
             (error 'num* "One of the arguments is not a number")]))

; Interpreter
(define (interp [a : ExprC] [env : Env]) : Value
  (type-case ExprC a
    ; Numbers just evaluta to their equivalent Value
    [numC (n) (numV n)]

    ; IDs are retrieved from the Env and unboxed
    [idC (n) (unbox (lookup n env))]

    ; Lambdas evaluate to closures, which save the environment
    [methodC (name arg body) (methodV name arg body)]

    ; Application of function
    ;[appC (f a)
    ;      (let ([f-value (interp f env)])
    ;        (interp (closV-body f-value)
    ;                (extend-env
    ;                    (bind (closV-arg f-value) (box (interp a env)))
    ;                    (closV-env f-value)
    ;                )))]

    ; Sum two numbers using auxiliary function
    [plusC (l r) (num+ (interp l env) (interp r env))]

    ; Multiplies two numbers using auxiliary function
    [multC (l r) (num* (interp l env) (interp r env))]

    ; Conditional operator
    [ifC (c s n) (if (zero? (numV-n (interp c env))) (interp n env) (interp s env))]

    ; Sequence of operations
    [seqC (b1 b2) (begin (interp b1 env) (interp b2 env))] ; No side effect between expressions!

    ; Attribution of variables
    [setC (var val) (let ([b (lookup var env)])
                      (begin (set-box! b (interp val env)) (unbox b)))]

    ; Declaration of variable
    [letC (name arg body)
          (let* ([new-bind (bind name (box (interp arg env)))]
                 [new-env (extend-env new-bind env)])
            (interp body new-env))]

    ; Declaration of a class
    [classC (pai var m1 m2)
            (classV pai var (interp m1 env) (interp m2 env))]

    ; Create a new object
    [newC (name val)
          (createObject name (interp val env) env)]

    [sendC (obj metName arg)
           (let* ([OBJ (interp obj env)]
                  [ARG (interp arg env)]
                  [R (findMethod OBJ OBJ metName ARG env)]
                  [met (res-met R)]
                  [menv (res-env R)])
               (interp (methodV-body met)
                       menv))]
    ))


; Parser
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (case (s-exp->symbol (first sl))
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (bminusS (parse (second sl)) (parse (third sl)))]
         [(~) (uminusS (parse (second sl)))]
         [(method) (methodS (s-exp->symbol (second sl)) (s-exp->symbol (third sl)) (parse (fourth sl)))] ; definição
         ;[(call) (appS (parse (second sl)) (parse (third sl)))]
         [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(seq) (seqS (parse (second sl)) (parse (third sl)))]
         [(:=) (setS (s-exp->symbol (second sl)) (parse (third sl)))]
         [(let) (letS (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl))))))
                      (parse (second (s-exp->list (first (s-exp->list (second sl))))))
                      (parse (third sl)))]
         [(new) (newS (s-exp->symbol (second sl)) (parse (third sl)))]         
         [(class) (classS (s-exp->symbol (second sl)) (s-exp->symbol (third sl))
                          (parse (fourth sl)) (parse (list-ref sl 4)))]
         [(send) (sendS (parse (second sl)) (s-exp->symbol (third sl)) (parse (fourth sl)))]
         
         [else (error 'parse "invalid list input")]))]
    [else (error 'parse "invalid input")]))


; Facilitator
(define (interpS [s : s-expression]) (interp (desugar (parse s)) (extend-env (bind 'Object (box Object)) mt-env)))

;
; Append this file in the end of your code to run the tests
;

; Test #0: Method call when instantiating Object
(test/exn
  (interpS
    '(let ([obj (new Object 0)])
       (send obj blah 42))) ; <-- Method does not exist!
  "Class does not respond to the method blah")

; Test #1: User-defiend class inheriting from Object, with methods that change
;          the attribute of the object (shared between them).
(test
  (interpS
    '(let ([Wallet
             (class Object money
                    (method credit amount (:= money (+ money amount)))
                    (method debit amount (:= money (- money amount))) )])
       (let ([wallet (new Wallet 0)])
         (seq (send wallet credit 10)
              (send wallet debit 3)))))
  (numV 7))

; Test #2: User-defined class inheriting from Object, with method that delegates
;          to another via self.
(test
  (interpS
    '(let ([Wallet
             (class Object money
                    (method credit amount (:= money (+ money amount)))
                    (method debit amount (send self credit (~ amount))) )])
       (let ([wallet (new Wallet 0)])
         (seq (send wallet credit 10)
              (send wallet debit 3)))))
  (numV 7))

; Test #3: User-defined class inheriting from Object, calling a method that does
;          not exist.
(test/exn
  (interpS
    '(let ([Wallet
             (class Object money
                    (method credit amount (:= money (+ money amount)))
                    (method debit amount (send self credit (~ amount))) )])
       (let ([wallet (new Wallet 0)])
         (seq (send wallet credit 10)
              (send wallet deduction 3))))) ; <-- Method does not exist!
  "Class does not respond to the method deduction")

; Test #4: User-define class inheriting from another user-defined class,
;          with method from child overriding the parent's implementation,
;          method from parent delegating to overriden method, and method
;          from child accessing attribute of the parent.
(test
  (interpS '(let ([Wallet
                    (class Object money
                           (method credit amount (:= money (+ money amount)))
                           (method debit amount (send self credit (~ amount))) )])
              (let ([WalletWithTaxes
                      (class Wallet tax
                             (method credit amount (:= money (- (+ money amount) tax)))
                             (method total dummy money) )])
                (let ([wallet (new WalletWithTaxes 1)])
                  (seq (send wallet credit 10)
                       (seq (send wallet debit 3)
                            (send wallet total 0))
                       )))))
  (numV 5))

; Test #5: User-define class inheriting from another user-defined class,
;          calling a method that does not exist.
(test/exn
  (interpS '(let ([Wallet
                    (class Object money
                           (method credit amount (:= money (+ money amount)))
                           (method debit amount (send self credit (~ amount))) )])
              (let ([WalletWithTaxes
                      (class Wallet tax
                             (method credit amount (:= money (- (+ money amount) tax)))
                             (method total dummy money) )])
                (let ([wallet (new WalletWithTaxes 1)])
                  (seq (send wallet credit 10)
                       (seq (send wallet debit 3)
                            (send wallet amount 0)) ; <-- Method does not exist!
                       )))))
  "Class does not respond to the method amount")
