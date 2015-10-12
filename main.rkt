#lang racket/base
(require (for-syntax racket/base)
         racket/runtime-path)

(define-runtime-module-path-index pb 'lang/plt-pretty-big)
(define-runtime-path prog "animation.rkt")

(namespace-require pb)
(load prog)