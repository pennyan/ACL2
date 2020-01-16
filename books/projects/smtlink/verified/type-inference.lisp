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

(include-book "type-inference-bottomup")
(include-book "type-inference-topdown")

(set-state-ok t)

(define construct-type-options ((smtlink-hint smtlink-hint-p))
  :returns (type-options type-options-p)
  :irrelevant-formals-ok t
  :ignore-ok t
  (b* ((smtlink-hint (smtlink-hint-fix smtlink-hint)))
    (make-type-options)))

(define type-judge-fn ((cl pseudo-term-listp)
                       (smtlink-hint t)
                       state)
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint))
        (list cl))
       ((smtlink-hint h) smtlink-hint)
       (goal (disjoin cl))
       ;; (options (construct-type-options smtlink-hint)) ;; TODO
       (options (construct-type-options smtlink-hint))
       (type-judgements (type-judgement goal ''t options state))
       (new-cl `((implies ,type-judgements ,goal)))
       (next-cp (cdr (assoc-equal 'type-judge *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',h state)))
       (hinted-goal `((hint-please ',the-hint) ,@new-cl)))
    (list hinted-goal)))

(define type-judge-cp ((cl pseudo-term-listp)
                       (hints t)
                       state)
  (b* ((new-clause (type-judge-fn cl hints state)))
    (value new-clause)))

(local (in-theory (enable type-judge-cp type-judge-fn)))

(skip-proofs
 (defthm correctness-of-type-judge-cp
   (implies (and (ev-smtcp-meta-extract-global-facts)
                 (pseudo-term-listp cl)
                 (alistp a)
                 (ev-smtcp
                  (conjoin-clauses
                   (acl2::clauses-result
                    (type-judge-cp cl hint state)))
                  a))
            (ev-smtcp (disjoin cl) a))
   :rule-classes :clause-processor)
 )
