#lang racket
(require racket/promise)

(define prog
  (let ([setFst (lambda (d x)
                  (match d
                         [`(,_ ,y) `(,x ,y)]
                         [`bot `(,x bot)]))]
        [setSnd (lambda (d y)
                  (match d
                         [`(,x ,_) `(,x ,y)]
                         [`bot `(bot ,y)]))]
        [getFst (lambda (d) (match d [`(,x ,_) (force x)]))]
        [getSnd (lambda (d) (match d [`(,_ ,y) (force y)]))])
    (getFst (setSnd (setFst `bot (lazy 42)) (lazy ((lambda (x) (x x)) (lambda (x) (x x))))))))

(print prog)
