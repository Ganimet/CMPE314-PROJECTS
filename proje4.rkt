
;;GANIMET YIGIT
;;112200078
;;PROJECT4-CMPE 314

#lang plai-typed

(define-type ExprS
  [numS (n : number)]
  [plusS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [idS (s : symbol)]
  [appS (fun : symbol) (arg : ExprS)])
;;ExprC 
;;S->number  S->symbol  S->S    S->S+ S     S->S*S   S->F  S->ε
; S->( λ(list of symbol) (S))  S->(S S S)

;S→F(a,b,c)   F(x,y,z)→xyz
;The grammar above is equivalent to the following because x, y, and z are substituted:
;S→abc
;Now suppose we leverage the function capability with the following grammar:
;S→F(ε)          F(x)→x a | x a F(x b)         (ε means empty string)

;;Defines datatype for ExprC
(define-type ExprC
  [numC (n : number)]
  [idC (s : symbol)]
  [appC (fun : symbol) (arg : ExprC)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)])

;;ExtendedMPF - Language with First Class Multi Parameter Functions
;;Grammar of ExtendedMPF
;;ExtendedMPF -> number
;;ExtendedMPF -> symbol
;;ExtendedMPF -> (+ ExtendedMPF ExtendedMPF)
;;ExtendedMPF -> (- ExtendedMPF ExtendedMPF)
;;ExtendedMPF -> (* ExtendedMPF ExtendedMPF)
;;ExtendedMPF -> (λ (listof symbol) (ExtendedMPF))
;;ExtendedMPF -> (ExtendedMPF ExtendedMPF ExtendedMPF)
;;ExtendedMPF Data Definition

(define-type ExtendedMPF
  [ExtendedMPFnum (n : number)]
  [ExtendedMPFadd (lhs : ExtendedMPF) (rhs : ExtendedMPF)]
  [ExtendedMPFsub (lhs : ExtendedMPF) (rhs : ExtendedMPF)]
  [ExtendedMPFmul (lhs : ExtendedMPF) (rhs : ExtendedMPF)]
  [ExtendedMPFid (s : symbol)]
  [ExtendedMPFlam (params : (listof symbol)) (body : ExtendedMPF)]
  [ExtendedMPFifzero (pred : ExtendedMPF)(truestate : ExtendedMPF)(falsestate : ExtendedMPF)])
;;Defines datatype for function definitions
;;function definitions have a name, one argument, and a body

(define-type FunDefC
  [fdC (name : symbol) (arg : symbol) (body : ExprC)])

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
         [(u-) (uminusS (parse (second sl)))]
         [else (appS (s-exp->symbol (first sl))
                     (parse (second sl)))]))]
    [else (error 'parse "invalid input")]))

(define (parsedef [s : s-expression]) : FunDefC
  (cond
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (case (s-exp->symbol (first sl))
         [(define) (fdC (s-exp->symbol (first (s-exp->list (second sl))))
                        (s-exp->symbol (second (s-exp->list (second sl))))
                        (desugar (parse (third sl))))]
         [else (error 'parsedef "invalid list")]))]
    [else (error 'parsedef "invalid input")]))

(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS (n) (numC n)]
    [plusS (l r) (plusC (desugar l)
                        (desugar r))]
    [multS (l r) (multC (desugar l)
                        (desugar r))]
    [bminusS (l r) (plusC (desugar l)
                          (multC (numC -1) (desugar r)))]
    [uminusS (e) (multC (numC -1)
                        (desugar e))]
    [idS (s) (idC s)]
    [appS (fun arg) (appC fun (desugar arg))]))

;; substitution of replacing a name in an expr with another expr 
;; what = what we want to replace the name with
;; for = what name we want to perform substitution
;; in = in which expression we want to do it
;; subst : ExprC * symbol * ExprC -> ExprC
(define (subst [what : ExprC] [for : symbol] [in : ExprC]) : ExprC
  (type-case ExprC in
    [numC (n) in]
    [idC (s) (cond
               [(symbol=? s for) what]
               [else in])]
    [appC (f a) (appC f (subst what for a))]
    [plusC (l r) (plusC (subst what for l)
                        (subst what for r))]
    [multC (l r) (multC (subst what for l)
                        (subst what for r))]))
;; get-fundef : symbol (listof FunDefC) -> FunDefC
;; Purpose : To find given symbol's(function name/identifier) function definition
;; - from function definition namespace.
;; Template : Basic Structural Recursion  
(define (get-fundef [n : symbol] [fds : (listof FunDefC)]) : FunDefC
  (cond
    [(empty? fds) (error 'get-fundef "reference to undefined function")]
    [(cons? fds) (cond
                   [(equal? n (fdC-name (first fds))) (first fds)]
                   [else (get-fundef n (rest fds))])]))
(define myFun(list
 
  (fdC 'double 'x (plusC (idC 'x) (idC 'x))) 
  (fdC 'inc5 'x (multC (idC 'x) (idC 'x)))))
(test (get-fundef 'double myFun) (fdC 'double 'x (plusC (idC 'x) (idC 'x))))
 (test (get-fundef 'inc5 myFun) (fdC 'inc5 'x (multC (idC 'x) (idC 'x)))) 
;;lookup function takes n as a symbol and environment which includes binding values,
;; then it checks wheter this funciton in environment or not?
;;if there is,it produces value otherwise it gives error

(define (lookup [n : symbol] [env : Env]) : number
  (cond
    [(empty? env) (error 'lookup "Symbol not found in env")]
    [(cons? env) (cond
                   [(equal? n (bind-name (first env))) (bind-val (first env))]
                   [else (lookup n (rest env))])]))
;Binding
;this function takes symbol as name and value which is number
;to bind any funciton

(define-type Binding
  [bind (name : symbol) (val : number)])

;; An alias to work easily on Environment.
(define-type-alias Env (listof Binding))

;; Empty environment.
(define mt-env empty)

;; Extending environment
(define extend-env cons)

(define-type Value
  [numvalue (n : number)]
  [functionvalue (params : (listof symbol)) (body : ExtendedMPF) (env : Env)])

(define (interp [expr : ExprC] [env : Env] [fds : (listof FunDefC)]) : number
  (type-case ExprC expr
    [numC (n) n]
    [idC (n) (lookup n env)]
    [appC (f a) (local ([define fd (get-fundef f fds)])
                  (interp (fdC-body fd)
                          (extend-env (bind (fdC-arg fd)
                                            (interp a env fds))
                                      mt-env)
                          fds))]
    [plusC (l r) (+ (interp l env fds) (interp r env fds))]
    [multC (l r) (* (interp l env fds) (interp r env fds))]))
 ; [ifC (pred t f)
  ;           (if (= 0 (numC (interp pred env)))
   ;             (interp t env   (interp f env)))])
(test (interp (plusC (numC 10) (appC 'const5 (numC 10)))
              mt-env
              (list (fdC 'const5 '_ (numC 5))))
      15)
 
(test (interp (plusC (numC 10) (appC 'double (plusC (numC 1) (numC 2))))
              mt-env
              (list (fdC 'double 'x (plusC (idC 'x) (idC 'x)))))
      16)
 
(test (interp (plusC (numC 10) (appC 'quadruple (plusC (numC 1) (numC 2))))
              mt-env
              (list (fdC 'quadruple 'x (appC 'double (appC 'double (idC 'x))))
                    (fdC 'double 'x (plusC (idC 'x) (idC 'x)))))
      22)

(test (interp (multC (numC 10 ) (appC 'double (plusC (numC 1) (numC 2))))
              mt-env
              (list (fdC 'quadruple 'x (appC 'double (appC 'double (idC 'x))))
                    (fdC 'double 'x (plusC (idC 'x) (idC 'x)))))
      60)

;; parse : s-exp -> ExtendedMPF
;; Purpose : To parse given s-exp to abstract syntax ExtendedMPF
;; Template : 
;(define (parse [s : s-expression]) : ExtendedMPF
;  (cond
;    [n ...]
;    [id ...]
;    [add ...]
;    [sub ...]
;    ))

(define (parse2 [s : s-expression]) : ExtendedMPF
  (cond
    [(s-exp-number? s) (ExtendedMPFnum (s-exp->number s))]
    [(s-exp-symbol? s) (ExtendedMPFid (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (cond
         [(and(= (length sl) 3)
          (symbol=? (s-exp->symbol (first sl)) '+))
          (ExtendedMPFadd (parse2 (second sl)) (parse2 (third sl)))]   
         [(and(= (length sl) 3)
          (symbol=? (s-exp->symbol (first sl)) '-))
          (ExtendedMPFsub (parse2 (second sl)) (parse2 (third sl)))]
         [(and(= (length sl) 3)
          (symbol=? (s-exp->symbol (first sl)) '*))
          (ExtendedMPFmul (parse2 (second sl)) (parse2 (third sl)))]
         [(and (= (length sl) 3) 
          (symbol=? (s-exp->symbol (first sl)) 'λ))
          (ExtendedMPFlam (map (lambda (x) (s-exp->symbol x))
                       (s-exp->list(second sl)))
                  (parse2 (third sl)))]
         [(= (length sl) 4)
          (case (s-exp->symbol (first sl))
            [(ifzero) (ExtendedMPFifzero 
                       (parse2 (second sl))
                       (parse2 (third sl))
                       (parse2 (fourth sl)))]
            [else (error 'parse2 "invalid keyword !")]
            )]              
         [else (error 'parse2 "invalid list input")])
       )]
    [else (error 'parse2 "invalid input")]))

    
;; TEST

(test (parse2 '(ifzero 5 10 2))(ExtendedMPFifzero (ExtendedMPFnum 5)(ExtendedMPFnum 10)(ExtendedMPFnum 2)))
(test (parse2 '(ifzero (* 4 5) 2 3)) (ExtendedMPFifzero (ExtendedMPFmul (ExtendedMPFnum 4) (ExtendedMPFnum 5)) (ExtendedMPFnum 2) (ExtendedMPFnum 3)))

(test (parse2 (number->s-exp 100))(ExtendedMPFnum 100))
(test (parse2 (symbol->s-exp 'x))(ExtendedMPFid 'x))

(test (parse2 '(+ 10 2)) (ExtendedMPFadd (ExtendedMPFnum 10) (ExtendedMPFnum 2)))
(test (parse2 '(- 40 15)) (ExtendedMPFsub (ExtendedMPFnum 40) (ExtendedMPFnum 15)))
(test (parse2 '(* 3 5)) (ExtendedMPFmul (ExtendedMPFnum 3) (ExtendedMPFnum 5)))

(parse2 '(λ (a b)(λ (c d)(* (+ a b)(- c d)))))
(parse2 '(λ (x y)(λ (a b)(+ (- x y)(* a b)))))
(parse2 '(λ (x z)(λ (a c)(+ (- x z)(* a c)))))
(parse2 '(λ (x y)(λ (a b)(+ (- x y)(* a b)))))
