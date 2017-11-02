#lang plai-typed

#|
 | Adding boxes, sequences with 2 expressions, variables and lists
 |#

; Breno Helfstein Moura
; 9790972

(define-type ExprC
  [numC    (n : number)]
  [idC     (s : symbol)]
  [plusC   (l : ExprC) (r : ExprC)]
  [multC   (l : ExprC) (r : ExprC)]
  [lamC    (arg : symbol) (body : ExprC)]
  [appC    (fun : ExprC) (arg : ExprC)]
  [ifC     (cond : ExprC) (y : ExprC) (n : ExprC)]
  [boxC    (arg : ExprC)]; Create a box
  [unboxC  (arg : ExprC)]; Unpacks the value inside a box
  [setboxC (b : ExprC) (v : ExprC)]; Replaces the value inside a box
  [seqC    (b1 : ExprC) (b2 : ExprC)]; Executes b1 then b2
  [consC   (car : ExprC) (cdr : ExprC)]; Creates cell with a pair
  [carC    (pair : ExprC)]; Gets 1st element of a pair
  [cdrC    (pair : ExprC)]; Gets 2nd element of a pair
  [setC    (var : symbol) (arg : ExprC)]; Attribution of variable
  [equalC  (a : ExprC) (b : ExprC)]
  [letrecC (s : symbol) (f : ExprC) (b : ExprC)]
  )


(define-type ExprS
  [numS    (n : number)]
  [idS     (s : symbol)] 
  [lamS    (arg : symbol) (body : ExprS)]
  [appS    (fun : ExprS) (arg : ExprS)] 
  [plusS   (l
            : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [multS   (l : ExprS) (r : ExprS)]
  [ifS     (c : ExprS) (y : ExprS) (n : ExprS)]
  [boxS    (a : ExprS)]
  [unboxS  (a : ExprS)]
  [setboxS (b : ExprS) (v : ExprS)]
  [seqS    (b1 : ExprS) (b2 : ExprS)]
  [consS   (car : ExprS) (cdr : ExprS)]
  [carS    (pair : ExprS)]
  [cdrS    (pair : ExprS)]
  [setS    (var : symbol) (arg : ExprS)]
  [equalS  (a : ExprS) (b : ExprS)]
  [letS    (s : symbol) (val  : ExprS) (body : ExprS)]
  [let*S   (s1 : symbol) (val1 : ExprS) (s2 : symbol) (val2 : ExprS) (body : ExprS)]
  [letrecS (s : symbol) (f : ExprS) (b : ExprS)]
  )


(define (desugar [as : ExprS]) : ExprC  
  (type-case ExprS as
    [numS    (n)        (numC n)]
    [idS     (s)        (idC s)]
    [lamS    (a b)      (lamC a (desugar b))]
    [appS    (fun arg)  (appC (desugar fun) (desugar arg))] 
    [plusS   (l r)      (plusC (desugar l) (desugar r))] 
    [multS   (l r)      (multC (desugar l) (desugar r))]
    [bminusS (l r)      (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS (e)        (multC (numC -1) (desugar e))]
    [ifS     (c y n)    (ifC (desugar c) (desugar y) (desugar n))]
    [boxS    (a)        (boxC   (desugar a))]
    [unboxS  (a)        (unboxC (desugar a))]
    [setboxS (b v)      (setboxC (desugar b) (desugar v))]
    [seqS    (b1 b2)    (seqC (desugar b1) (desugar b2))]
    [consS   (b1 b2)    (consC (desugar b1) (desugar b2))]
    [carS    (c)        (carC (desugar c))]
    [cdrS    (c)        (cdrC (desugar c))]
    [setS    (var expr) (setC  var (desugar expr))]
    [equalS  (a b)      (equalC (desugar a) (desugar b))]
    [letS    (s val body) (appC (lamC s (desugar body)) (desugar val))]
    [let*S   (s1 val1 s2 val2 body) (appC (lamC s1 (appC (lamC s2 (desugar body)) (desugar val2))) (desugar val1))]
    [letrecS (s f b) (letrecC s (desugar f) (desugar b))]
    ))


; We need storage and location
(define-type-alias Location number)

; We need a new value for the box
(define-type Value
  [numV  (n : number)]
  [closV (arg : symbol) (body : ExprC) (env : Env)]
  [boxV  (l : Location)] ; Points to the location
  [consV (car : Location) (cdr : Location)]
  [suspV (body : ExprC) (env : Env)]
  )


; Bindings associate symbol with location
(define-type Binding
        [bind (name : symbol) (val : Location)])

; Env remains the same, we only change the Binding
(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)


; Storage's operations are similar to Env's
;   bind <-> cell
;   mt-env <-> mt-store
;   extend-env <-> override-store
(define-type Storage
      [cell (location : Location) (val : (boxof Value))])
(define-type-alias Store (listof Storage))

(define mt-store empty)
(define override-store cons)


; lookup changes its return type
(define (lookup [for : symbol] [env : Env]) : Location
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string for) " não foi encontrado"))] ; livre (não definida)
            [else (cond
                  [(symbol=? for (bind-name (first env)))   ; achou!
                                 (bind-val (first env))]
                  [else (lookup for (rest env))])]))        ; vê no resto

; fetch is equivalent to a lookup for the store
(define (fetch [l : Location] [sto : Store]) : Value
       (cond
            [(empty? sto) (error 'fetch "posição não encontrada")]
            [else (cond
                  [(= l   (cell-location (first sto)))   ; achou!
                   (unbox (cell-val (first sto)))]
                  [else (fetch l (rest sto))])]))        ; vê no resto

(define (update [l : Location] [sto : Store] [Isto : Store]) : Result
       (cond
            [(empty? sto) (error 'update "posição não encontrada")]
            [else (cond
                  [(= l   (cell-location (first sto)))   ; achou!
                   (let* ([V (unbox (cell-val (first sto)))]
                          [res (interp (suspV-body V) (suspV-env V) Isto)])
                     (begin (set-box! (cell-val (first sto)) (v*s-v res))
                            [v*s (unbox (cell-val (first sto))) (v*s-s res)]))]
                  [else (update l (rest sto) Isto)])]))        ; vê no resto
  
; Returns the next location available
(define new-loc
   (let ( [ n (box 0)])
        (lambda () 
           (begin
              (set-box! n (+ 1 (unbox n)))
              (unbox n)))))


; Auxiliar operators
(define (num+ [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (+ (numV-n l) (numV-n r)))]
        [else
             (error 'num+ "Um dos argumentos não é número")]))

(define (num* [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (* (numV-n l) (numV-n r)))]
        [else
             (error 'num* "Um dos argumentos não é número")]))


; New return type for our interpreter, Env and Store
(define-type Result
      [v*s (v : Value) (s : Store)])

(define (result-equal a b sto)
  (cond
    [(and (consV? a) (consV? b))
     (let* ([carA (fetch (consV-car a) sto)]
            [cdrA (fetch (consV-cdr a) sto)]
            [carB (fetch (consV-car b) sto)]
            [cdrB (fetch (consV-cdr b) sto)])
             (begin (when (suspV? carA) (let ([res (update (consV-car a) sto sto)]) (begin (set! carA (v*s-v res)) (set! sto (v*s-s res)))))
                    (when (suspV? cdrA) (let ([res (update (consV-cdr a) sto sto)]) (begin (set! cdrA (v*s-v res)) (set! sto (v*s-s res)))))
                    (when (suspV? carB) (let ([res (update (consV-car b) sto sto)]) (begin (set! carB (v*s-v res)) (set! sto (v*s-s res)))))
                    (when (suspV? cdrB) (let ([res (update (consV-cdr b) sto sto)]) (begin (set! cdrB (v*s-v res)) (set! sto (v*s-s res))))) 
                    (if (and (result-equal carA carB sto) (result-equal cdrA cdrB sto))
             #t
             #f)))]
    [(and (boxV? a) (boxV? b))
     (if (result-equal (fetch (boxV-l a) sto) (fetch (boxV-l b) sto) sto)
         #t
         #f)]
    [(and (not (consV? a)) (not (consV? b)))
     (if (equal? a b)
         #t
         #f)]
    [else #f]
    ))

; interp receives and returns Store
(define (interp [a : ExprC] [env : Env] [sto : Store]) : Result
  (type-case ExprC a
    [numC (n) (v*s (numV n) sto)]
    [idC (n)  (let ([V (fetch (lookup n env) sto)])
                (if (suspV? V) (update (lookup n env) sto sto)
                    (v*s V sto)))]; cascading search, first in env then in sto
    [lamC (a b) (v*s (closV a b env) sto)]
    
    [seqC (b1 b2) (type-case Result (interp b1 env sto)
                    [v*s (v-b1 s-b1) ; result and store retorned by b1
                          (interp b2 env s-b1)])]
                          
    ; application of function
    [appC (f a)
          (type-case Result (interp f env sto) ; find the function
            [v*s (v-f s-f)
                 (let ([where (new-loc)]) ; allocs position for the value of the argument
                   (interp (closV-body v-f) ; body
                           (extend-env (bind (closV-arg v-f) where) ; with new argument
                                       (closV-env v-f))
                           (override-store (cell where (box (suspV a env))) s-f))) ; with new value
                 ])]
    
    [plusC (l r) 
           (type-case Result (interp l env sto)
               [v*s (v-l s-l)
                    (type-case Result (interp r env s-l)
                      [v*s (v-r s-r)
                           (v*s (num+ v-l v-r) s-r)])])]
                           
    [multC (l r) 
           (type-case Result (interp l env sto)
               [v*s (v-l s-l)
                    (type-case Result (interp r env s-l)
                      [v*s (v-r s-r)
                           (v*s (num* v-l v-r) s-r)])])]
                           
    ; ifC serializes
    [ifC (c s n) (type-case Result (interp c env sto)
                   [v*s (v-c- s-c)
                        (if (zero? (numV-n (v*s-v (interp c env sto))))
                            (interp n env s-c)
                            (interp s env s-c))])]
    
    ; Creates a box: it needs a value and a new location
    [boxC (a) 
          (type-case Result (interp a env sto)
            [v*s (v-a s-a)
                 (let ([where (new-loc)])
                   (v*s (boxV where) 
                        (override-store (cell where (box v-a)) s-a)))])]
                        
    ; Get the value from a box                
    [unboxC (a) (type-case Result (interp a env sto)
                  [v*s (v-a s-a)
                       (v*s 
                        (fetch (boxV-l v-a) s-a) ; value
                        s-a                      ; store
                        )])]

    ; Replace the value inside a box
    [setboxC (b v) (type-case Result (interp b env sto); Result is a pair
                     [v*s (v-b s-b)
                          (type-case Result (interp v env s-b)
                            [v*s (v-v s-v)
                                 (v*s v-v
                                      (override-store 
                                       (cell (boxV-l v-b)
                                             (box v-v))
                                       s-v))])])]
    ; Attribution of variables
    [setC (var val) (type-case Result (interp val env sto)
                      [v*s (v-val s-val)
                           (let ([where (lookup var env)]) ; finds the variable
                             (v*s v-val
                                  (override-store ; updates
                                   (cell where (box v-val)) s-val)))])]
    
    ; Working with lists
    [consC (b1 b2)
           (let ((where-b1 (new-loc)) (where-b2 (new-loc)))
                  (v*s (consV where-b1 where-b2)
                       (override-store (cell where-b2 (box (suspV b2 env)))
                                       (override-store (cell where-b1 (box (suspV b1 env)))
                                                       sto))))]
    
    [carC (c) (type-case Result (interp c env sto)
                [v*s (v-c s-c)
                     [let ([V (fetch (consV-car v-c) s-c)]) 
                       (if (suspV? V) (update (consV-car v-c) s-c s-c)
                           (v*s V s-c))]])]
                          
    [cdrC (c) (type-case Result (interp c env sto)
                [v*s (v-c s-c)
                     [let ([V (fetch (consV-cdr v-c) s-c)]) 
                       (if (suspV? V) (update (consV-cdr v-c) s-c s-c)
                           (v*s V s-c))]])]

    [equalC (a b) (type-case Result (interp a env sto)
               [v*s (v-a s-a)
                    (type-case Result (interp b env s-a)
                      [v*s (v-b s-b)
                           [v*s (if (result-equal v-a v-b s-b) (numV 1) (numV 0)) s-b]
                                  ])])]

    [letrecC (s f b) (type-case Result (let* (
                      [closD (closV 'dummy (idC s) env)]
                      [where (new-loc)]
                      [func  (interp f (extend-env (bind s where) env) (override-store (cell where (box closD)) sto))])                                     
                      (interp b (extend-env (bind s where) env) (override-store (cell where (box (v*s-v func))) sto)))
                       [v*s (v-b s-b)
                            (v*s v-b s-b)])]
    ))

(define (calcCons b1 b2 env sto)
  (type-case Result (interp b1 env sto)
    [v*s (v-b1 s-b1)
         (type-case Result (interp b2 env s-b1)
           [v*s (v-b2 s-b2)
                (let ((where-b1 (new-loc)) (where-b2 (new-loc)))
                  (v*s (consV where-b1 where-b2)
                       (override-store (cell where-b2 (box v-b2))
                                       (override-store (cell where-b1 (box v-b1))
                                                       s-b2))))])]))

(define (calcApp f a env sto)
  (type-case Result (interp f env sto) ; find the function
    [v*s (v-f s-f)
         (type-case Result (interp a env s-f) ; argument with sto changed by the function
           [v*s (v-a s-a)
                (let ([where (new-loc)]) ; allocs position for the value of the argument
                  (interp (closV-body v-f) ; body
                          (extend-env (bind (closV-arg v-f) where) ; with new argument
                                      (closV-env v-f))
                          (override-store (cell where (box v-a)) s-a))) ; with new value
                ])]))

; Parser with funny instructions for boxes
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))] ; pode ser um símbolo livre nas definições de função
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (case (s-exp->symbol (first sl))
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (bminusS (parse (second sl)) (parse (third sl)))]
         [(~) (uminusS (parse (second sl)))]
         [(lambda) (lamS (s-exp->symbol (second sl)) (parse (third sl)))] ; definição
         [(call) (appS (parse (second sl)) (parse (third sl)))]
         [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(-#) (boxS (parse (second sl)))]
         [(>#) (unboxS (parse (second sl)))]
         [(!#) (setboxS (parse (second sl)) (parse (third sl)))]
         [(seq) (seqS (parse (second sl)) (parse (third sl)))]
         [(:=) (setS (s-exp->symbol (second sl)) (parse (third sl)))]
         [(cons) (consS (parse (second sl)) (parse (third sl)))]
         [(car) (carS (parse (second sl)))]
         [(cdr) (cdrS (parse (second sl)))]
         [(equal?) (equalS (parse (second sl)) (parse (third sl)))]
         [(let) (letS (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl)))))) (parse (second (s-exp->list (first (s-exp->list (second sl)))))) (parse (third sl)))]
         [(let*) (let*S (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl)))))) (parse (second (s-exp->list (first (s-exp->list (second sl)))))) (s-exp->symbol (first (s-exp->list (second (s-exp->list (second sl))))))
                        (parse (second (s-exp->list (second (s-exp->list (second sl)))))) (parse (third sl)))]
         [(letrec) (letrecS (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl)))))) (parse (second (s-exp->list (first (s-exp->list (second sl))))))
                            (parse (third sl)))]
         [else (error 'parse "invalid list input")]))]
    [else (error 'parse "invalid input")]))


; Facilitator
(define (interpS [s : s-expression]) (interp (desugar (parse s)) mt-env mt-store))


; Examples
(interpS '(+ 10 (call (lambda x (car x)) (cons 15 16))))

(interpS '(call (lambda x (seq (:= x (+ x 5))x)) 8))

(interpS '(seq (!# (-# 2) 32) (># (-# 2) (+ (># (-# 2)) 10))))

(interpS '(call (lambda f (call f (-# 32))) (lambda x (seq (!# x (+ (># x) 10)) (># x)))))


; Tests
(test (v*s-v (interp (carC (consC (numC 10) (numC 20)))
              mt-env mt-store))
      (numV 10))

(test (v*s-v (interpS '(equal? (cons 1 3) (cons 1 2)))) (numV 0))
(test (v*s-v (interpS '(equal? (cons (cons 1 2) (cons 1 2)) (cons (cons 1 2) (cons 1 2))))) (numV 1))
(test (v*s-v (interpS '(equal? (+ 1 2) (+ 1 3)))) (numV 0))
(test (v*s-v (interpS '(equal? (+ 1 2) (+ 1 2)))) (numV 1))
(test (v*s-v (interpS '(equal? 1 2))) (numV 0))
(test (v*s-v (interpS '(equal? 1 1))) (numV 1))
(test (v*s-v (interpS '(let ([x 1]) (equal? (cons x (:= x (+ x 1))) (cons (- x 1) x))))) (numV 1)) ;Não funciona por que não tem SupsV no setC

(test (v*s-v (interpS '(letrec ([fact (lambda n (if n (* n (call fact (- n 1))) 1))]) (call fact 5)))) (numV 120)) ; Teste do fatorial
(test (v*s-v (interpS '(letrec ([l (lambda n (cons n (call l (+ 1 n))))]) (car (call l 1))))) (numV 1)) ; Teste listas infinitas
(test (v*s-v (interpS '(letrec ([l (lambda n (cons n (call l (+ 1 n))))]) (car (cdr (call l 1)))))) (numV 2)) ; Teste listas infinitas
(test (v*s-v (interpS '(letrec ([l (lambda n (cons n (call l (+ 1 n))))]) (car (cdr (cdr (call l 1))))))) (numV 3)) ; Teste listas infinitas
;(interpS '(letrec ([l (lambda n (cons n (call l (+ 1 n))))]) (car (cdr (call l 1)))))
(interpS '(call (lambda x x) (+ 1 1)))
(interpS '(call (lambda x 10) (+ 1 1)))