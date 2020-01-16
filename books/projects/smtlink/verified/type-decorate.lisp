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
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)

(include-book "hint-please")
(include-book "basics")
(include-book "evaluator")

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
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (type-decorate-cp cl hint state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :rule-classes :clause-processor)
