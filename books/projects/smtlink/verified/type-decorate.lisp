;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (Dec 12th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic"
              :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)

(include-book "hint-please")
(include-book "basics")
;; -----------------------------------------------------------------
;;       Define evaluators
;; I might be able to merge evaluators into a single file and use the same
;;       evaluator across clause-processors.

(acl2::defevaluator-fast ev-decorate ev-decorate-lst
                         ((if a b c) (equal a b) (not a)
                          (cons a b) (binary-+ a b)
                          (typespec-check ts x)
                          (iff a b)
                          (implies a b)
                          (hint-please hint)
                          (return-last x y z)
                          (binary-+ x y))
                         :namedp t)

(acl2::def-ev-theoremp ev-decorate)
(acl2::def-meta-extract ev-decorate ev-decorate-lst)
(acl2::def-unify ev-decorate ev-decorate-alist)

;; -----------------------------------------------------------------


(define type-decorate-fn ((cl pseudo-term-listp)
                          (smtlink-hint t)
                          state)
  :returns (subgoal-lst pseudo-term-list-listp)
  :ignore-ok t
  :irrelevant-formals-ok t
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint))
        (list cl))
       ((smtlink-hint h) smtlink-hint)
       (new-cl cl)
       (next-cp (cdr (assoc-equal 'type-decorate *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',h state)))
       (hinted-goal `((hint-please ',the-hint) ,@new-cl)))
    (list hinted-goal)))

(define type-decorate-cp ((cl pseudo-term-listp)
                          (hints t)
                          state)
  (b* ((decorated-clause (type-decorate-fn cl hints state)))
    (value decorated-clause)))

(local (in-theory (enable type-decorate-cp type-decorate-fn)))

(defthm correctness-of-type-decorate-cp
  (implies (and (ev-decorate-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-decorate
                 (conjoin-clauses
                  (acl2::clauses-result
                   (type-decorate-cp cl hint state)))
                 a))
           (ev-decorate (disjoin cl) a))
  :rule-classes :clause-processor)

