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
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "hint-please")

;; -----------------------------------------------------------------
;;       Define evaluators

(acl2::defevaluator-fast ev-infer ev-infer-lst
                         ((if a b c) (equal a b) (not a)
                          (cons a b) (binary-+ a b)
                          (typespec-check ts x)
                          (iff a b)
                          (implies a b)
                          (hint-please hint)
                          (return-last x y z)
                          (binary-+ x y))
                         :namedp t)

(acl2::def-ev-theoremp ev-infer)
(acl2::def-meta-extract ev-infer ev-infer-lst)
(acl2::def-unify ev-infer ev-infer-alist)

(define is-conjunct? ((term pseudo-termp))
  :returns (ok booleanp)
  (b* ((term (pseudo-term-fix term)))
    (or (equal term 't)
        (and (consp term)
             (equal (car term) 'if)
             (consp (cdr term)) (consp (cddr term))
             (consp (cdddr term)) (equal (cadddr term) 'nil)
             (consp (cddddr term))))))

(define path-cond-implies-expr ((path-cond pseudo-termp) (expr pseudo-termp))
  :returns (ok booleanp)
  (b* ((path-cond (pseudo-term-fix path-cond))
       (expr (pseudo-term-fix expr))
       ((unless (is-conjunct? path-cond))
        (er hard? 'type-inference=>path-cond-implies-expr
            "Path condition is not a conjunction of conditions: ~q0" path-cond))
       ((if (equal path-cond 't)) nil)
       ((list & path-hd path-tl &) path-cond)
       (path-hd-nil/expr (term-substitution path-hd expr 'nil))
       ((if (null (eval-const-expr path-hd-nil/expr))) t))
    (path-cond-implies-expr path-tl expr)))
stop
(defines type-judgements

(define type-judgement ((term pseudo-termp) (path-cond pseudo-termp))
  :returns (judgements pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (path-cond (pseudo-term-fix path-cond))
       ((if (acl2::variablep term))
        )
       )
    ()))

(define type-judgement-list ((term-lst pseudo-term-listp)
                             (path-cond pseudo-termp))
  :returns (judgements-lst pseudo-term-listp)
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       (path-cond (pseudo-term-fix path-cond))
       ((unless (consp term-lst)) 't)
       ((cons first rest) term-lst)
       (first-judge (type-judgement first path-cond))
       (rest-judge (type-judgement-list rest path-cond)))
    `(if ,first-judge
         ,rest-judge
       'nil)))
  )

)
