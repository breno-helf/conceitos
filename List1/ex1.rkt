#lang racket
(define lista '(a b (c d) e))

(define teste '((a (b 5)) (c d) e))

(define (sigma m n) (if (equal? m n) n (+ m (sigma (+ m 1) n))))

(define (exp m n) (if (equal? n 0) 1 (* m (exp m (- n 1)))))

(define (log m n) (if (> m n) 0 (+ 1 (log m (/ n m)))))

(define (fib m) (if (equal? m 0) 0 (if (equal? m 1) 1 (+ (fib (- m 1)) (fib (- m 2))))))

(define (count x l) (if (equal? l '()) 0 (+ (if (equal? (car l) x) 1 0) (count x (cdr l)))))

(define (countall x l) (if (equal? l '()) 0 (+ (if (list? (car l)) (countall x (car l))
                                                   (if (equal? (car l) x) 1 0)) (countall x (cdr l)))))

(define (reverse l) (if (equal? (cdr l) '()) l (append (reverse (cdr l)) (list (car l)))))
