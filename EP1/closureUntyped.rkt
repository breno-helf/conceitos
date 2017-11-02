#lang plai

#|
 | Funções não têm mais nome, serão chamadas de lamC (em homenagem ao λ)
 |#

; Expressões básicas
(define-type ExprC
  [numC  (n  number?)]
  [idC   (s  symbol?)]
  [plusC (l  ExprC?) (r  ExprC?)]
  [multC (l  ExprC?) (r  ExprC?)]
  [lamC  (arg  symbol?) (body  ExprC?)] ; nomes não são mais necessários
  [appC  (fun  ExprC?) (arg  ExprC?)]
  [ifC   (condição  ExprC?) (sim  ExprC?) (não  ExprC?)]
  [quoteC (s symbol?)]
  [loadC  (f ExprC?)]
  [letrecC (s symbol?) (f ExprC?) (b ExprC?)]
  )


; Expressões açucaradas
(define-type ExprS
  [numS    (n  number?)]
  [idS     (s  symbol?)] 
  [lamS    (arg  symbol?) (body  ExprS?)] ; muda de acordo
  [appS    (fun  ExprS?) (arg  ExprS?)] 
  [plusS   (l  ExprS?) (r  ExprS?)]
  [bminusS (l  ExprS?) (r  ExprS?)]
  [uminusS (e  ExprS?)]
  [multS   (l  ExprS?) (r  ExprS?)]
  [ifS     (c  ExprS?) (s  ExprS?) (n  ExprS?)]
  [letS    (s  symbol?) (val  ExprS?) (body  ExprS?)]
  [let*S   (s1 symbol?) (val1 ExprS?) (s2 symbol?) (val2 ExprS?) (body ExprS?)]
  [letrecS (s symbol?) (f ExprS?) (b ExprS?)]
  [quoteS  (s  symbol?)]
  [loadS   (f  ExprS?)]
  )


; Retirando o açúcar
(define (desugar as); ExprS => ExprC  
  (type-case ExprS as
    [numS    (n) (numC n)]
    [idS     (s) (idC s)]
    [lamS    (a b)  (lamC a (desugar b))]
    [appS    (fun arg) (appC (desugar fun) (desugar arg))] 
    [plusS   (l r) (plusC (desugar l) (desugar r))] 
    [multS   (l r) (multC (desugar l) (desugar r))]
    [bminusS (l r) (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS (e)   (multC (numC -1) (desugar e))]
    [ifS     (c s n) (ifC (desugar c) (desugar s) (desugar n))]
    [letS    (s val body) (appC (lamC s (desugar body)) (desugar val))]
    [let*S   (s1 val1 s2 val2 body) (appC (lamC s1 (appC (lamC s2 (desugar body)) (desugar val2))) (desugar val1))]
    [letrecS (s f b) (letrecC s (desugar f) (desugar b))]
    [quoteS  (s) (quoteC s)]
    [loadS   (f) (loadC (desugar f))]
    ))


#|
 | Closures não têm mais nome, mas precisam de Environment
 |#

; Símbolos devem se associar a um Value
(define-type Binding
      [bind (name  symbol?) (val  Value?)])

; A lista de associações é o Environment
; (define-type-alias Env (listof Binding))
(define mt-env empty)    ; Tente pronunciar "mt" em inglês e compare com "empty"
(define extend-env cons) ; Por sorte, cons faz exatamente o que queremos para estender o env
(define-type Value
  [numV  (n  number?)]
  [closV (arg  symbol?) (body  ExprC?) (env  list?)]
  [symV  (s symbol?)])

; Novos operadores
(define (num+ l r); Value x Value => Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (+ (numV-n l) (numV-n r)))]
        [else
             (error 'num+ "Um dos argumentos não é número")]))

(define (num* l r); Value x Value => Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (* (numV-n l) (numV-n r)))]
        [else
             (error 'num* "Um dos argumentos não é número")]))

(define (interpFile s)
  (ReadFile (open-input-file (~a (symV-s s))))) 

; Le o arquivo e interpreta as linhas
(define (ReadFile f)
  ((lambda (line) (when (not (or (eof-object? line) (null? line))) (begin (println (interpS line)) (ReadFile f)))) (read f)))

; Interpretador
(define (interp a env); ExprC x Env => Value
  (type-case ExprC a
    [numC (n) (numV n)] 
    [idC (n) (lookup n env)]
    [lamC (a b) (closV a b env)] ; definição de função captura o environment

    [appC (f a)
          (local ([define f-value (interp f env)]) ; f-value descreve melhor a ideia
            (interp (closV-body f-value)
                    (extend-env 
                        (bind (closV-arg f-value) (interp a env))
                        (closV-env f-value) ; não mais mt-env
                    )))]
    [letrecC (s f b)
             (local ([define s-name (interp f env)])
               (begin (set-closV-env! s-name (extend-env (bind s s-name) env))
                      (interp b (extend-env (bind s s-name) env))))]

    [plusC (l r) (num+ (interp l env) (interp r env))]
    [multC (l r) (num* (interp l env) (interp r env))]
    [ifC (c s n) (if (zero? (numV-n (interp c env))) (interp n env) (interp s env))]
    [quoteC (s) (symV s)]
    [loadC  (f)
            (interpFile (interp f env))]
    ))

; Lookup para procurar símbolos no Environment
(define (lookup for env); [for : symbol] [env : Env]) => Value
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string for) " não foi encontrado"))] ; livre (não definida)
            [else (cond
                  [(symbol=? for (bind-name (first env)))   ; achou!
                                 (bind-val (first env))]
                  [else (lookup for (rest env))])]))        ; vê no resto


; Parser
(define (parse s); [s : s-expression] => ExprS
  (cond
    [(number? s) (numS s)]
    [(symbol? s) (idS  s)] ; Pode ser um símbolo livre nas definições de função
    [(list? s)
     (let ([sl s])
       (case  (first sl)
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (bminusS (parse (second sl)) (parse (third sl)))]
         [(~) (uminusS (parse (second sl)))]
         [(func) (lamS (second sl) (parse (third sl)))]
         [(lambda) (lamS (second sl) (parse (third sl)))]
         [(call) (appS (parse (second sl)) (parse (third sl)))]
         [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
         [(let) (letS (first (first (second sl))) (parse (second (first (second sl)))) (parse (third sl)))]
         [(let*) (let*S (first (first (second sl))) (parse (second (first (second sl)))) (first (second (second sl))) (parse (second (second (second sl))))
                        (parse (third sl)))]
         [(letrec) (letrecS (first (first (second sl))) (parse (second (first (second sl)))) (parse (third sl)))]
         [(quote) (quoteS (second sl))]
         [(load)  (loadS (parse (second sl)))]
         [else (error 'parse "invalid list input")]))]
    [else (error 'parse "invalid input")]))

; Facilitador
(define (interpS s) (interp (desugar (parse s)) mt-env))

; Testes
; Testes default
(test (interp (plusC (numC 10) (appC (lamC '_ (numC 5)) (numC 10)))
              mt-env)
      (numV 15))
(interpS '(+ 10 (call (func x (+ x x)) 16)))


(test (interpS '(quote test.txt)) (symV 'test.txt)) ; Teste do Quote

(test (interp (desugar (letS 'x (numS 3) (idS 'x))) mt-env) (numV 3)) ; Teste do letS

(test (interpS '(let ([x 3]) x)) (numV 3)) ; Teste do let
(test (interpS '(let* ([x 1] [y 2]) (+ x y))) (numV 3)) ; Teste do let*
(test (interpS '(let* ([x 2] [y x]) (+ x y))) (numV 4)) ; Teste do let*
(test (interpS '(letrec ([f (lambda n n)]) (call f 3))) (numV 3)) ; Test do letrec


(interpS '(load (quote test.txt))) ; Teste do load

(test (interpS '(call (lambda n n) 4)) (numV 4)) ; Testando lambda 

(test (interpS '(letrec ([fact (lambda n (if n (* n (call fact (- n 1))) 1))]) (call fact 5)))  (numV 120)) ; Teste do fatorial
