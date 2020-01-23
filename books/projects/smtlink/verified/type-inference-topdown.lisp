;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "typed-term")

(define unify-variable ((tterm typed-term-p))
  :guard (and (good-typed-term-p tterm)
              (equal (typed-term->kind tterm) 'variablep))
  :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (equal (typed-term->kind tterm) 'variablep)
                          (good-typed-term-p tterm))))
        (make-typed-term)))
    tterm))

(define unify-quote ((tterm typed-term-p))
  :guard (and (good-typed-term-p tterm)
              (equal (typed-term->kind tterm) 'quotep))
  :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (equal (typed-term->kind tterm) 'quotep)
                          (good-typed-term-p tterm))))
        (make-typed-term)))
    tterm))

(define unify-lambda ((tterm typed-term-p))
  :guard (and (good-typed-term-p tterm)
              (equal (typed-term->kind tterm) 'lambdap))
    :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt)))
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (equal (typed-term->kind tterm) 'lambdap)
                            (good-typed-term-p tterm))))
          (make-typed-term)))
      tterm))

  (define unify-if ((tterm typed-term-p))
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'ifp))
    :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt)))
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (equal (typed-term->kind tterm) 'ifp)
                            (good-typed-term-p tterm))))
          (make-typed-term))
         ;; ((typed-term tt) tterm)
         ;; (tt-cond (typed-term-if->cond tt))
         ;; (tt-then (typed-term-if->then tt))
         ;; (tt-else (typed-term-if->else tt))
         )
      tterm
      ;; (typed-term-if->cons tt-cond tt-then tt-else)
      ))

;; if: ?
;; implies: do i care?
;; not:
;; equal:
;; <:
;; binary-+, binary-*, unary--, unary-/:
;; cons, car, cdr, acons, assoc-equal:
;; user defined: select judgements that satisfies the function guard
  (define unify-fncall ((tterm typed-term-p))
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'fncallp))
    :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt)))
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (equal (typed-term->kind tterm) 'fncallp)
                            (good-typed-term-p tterm))))
          (make-typed-term)))
      tterm))

(define unify-type ((tterm typed-term-p))
  :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt)))
  :guard (good-typed-term-p tterm)
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (good-typed-term-p tterm))))
        (make-typed-term))
       ((if (equal (typed-term->kind tterm) 'variablep))
        (unify-variable tterm))
       ((if (equal (typed-term->kind tterm) 'quotep))
        (unify-quote tterm))
       ((if (equal (typed-term->kind tterm) 'lambdap))
        (unify-lambda tterm))
       ((if (equal (typed-term->kind tterm) 'ifp))
        (unify-if tterm)))
    (unify-fncall tterm)))

;; (defines unify-type
;;   :well-founded-relation l<
;;   :verify-guards nil

(define unify-type-list ((tterm-lst typed-term-list-p))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl)))
  :guard (good-typed-term-list-p tterm-lst)
  :measure (acl2-count (typed-term-list->term-lst tterm-lst))
  :verify-guards nil
  (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                          (good-typed-term-list-p tterm-lst))))
        (make-typed-term-list))
       ((typed-term-list ttl) tterm-lst)
       ((unless (typed-term-list-consp ttl)) ttl))
    (typed-term-list->cons (unify-type (typed-term-list->car ttl))
                           (unify-type-list (typed-term-list->cdr ttl)))))
;; )
