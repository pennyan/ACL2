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
(include-book "type-options")
(include-book "evaluator")
(include-book "typed-term")

(define rectify ((tterm typed-term-p)
                 (replace-name symbolp)
                 state)
  :guard (and (good-typed-term-p tterm)
              (equal (typed-term->kind tterm) 'fncallp))
  :returns (new-tt maybe-typed-term-p)
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
       ((cons fn actuals) tt.term)
       (replace-thm
        (acl2::meta-extract-formula-w replace-name (w state)))
       ((unless (pseudo-termp replace-thm))
        (mv (er hard? 'term-rectify=>rectify
                "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
                replace-name replace-thm)
            (make-typed-term)))
       ((mv err )
        (case-match replace-thm
          ((implies hypo (equal (!fn formals) (new-fn formals)))
           (b* ((yes? (path-test-)))
             (mv nil )))
          ((implies hypo (equal (new-fn formals) (!fn formals)))
           ())
          (& (mv t nil))))
       )
    ())
  ///
  (more-returns
   (new-tt (implies new-tt (good-typed-term-p new-tt))
           :name good-typed-term-p-of-rectify)))

(define rectify-list ((tterm typed-term-p)
                      (replace-name symbolp)
                      state)
  :guard (and (good-typed-term-p tterm)
              (equal (typed-term->kind tterm) 'fncallp))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt)))
  ()
  )

(defines term-rectify
  :well-founded-relation l<
  :verify-guards nil

  (define lambda-rectify ((tterm typed-term-p)
                          (options type-options-p)
                          state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'lambdap))
    :returns (new-tt (and (typed-term-p new-tt)
                          (good-typed-term-p new-tt)))
    :measure (list (acl2-count (typed-term->term tterm))
                   0)
    (b* ((tterm (typed-term-fix tterm))
         ((unless (mbt (and (good-typed-term-p tterm)
                            (equal (typed-term->kind tterm) 'lambdap))))
          (make-typed-term))
         ((typed-term tt) tterm)
         (formals (lambda-formals (car tt.term)))
         (tta (typed-term-lambda->actuals tterm options))
         (ttb (typed-term-lambda->body tterm options))
         ((typed-term rtta) (term-list-rectify tta options state))
         ((typed-term rttb) (term-rectify ttb options state)))
      (make-typed-term :term `((lambda ,formals ,rttb.term) ,@rtta.term)
                       :path-cond tt.path-cond
                       :judgements tt.judgements)))

  (define if-rectfify ((tterm typed-term-p)
                       (options type-options-p)
                       state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'ifp))
    :returns (new-tt (and (typed-term-p new-tt)
                          (good-typed-term-p new-tt)))
    :measure (list (acl2-count (typed-term->term tterm))
                   0)
    (b* ((tterm (typed-term-fix tterm))
         ((unless (mbt (and (good-typed-term-p tterm)
                            (equal (typed-term->kind tterm) 'ifp))))
          (make-typed-term))
         ((typed-term tt) tterm)
         (ttc (typed-term-if->cond tt to))
         (ttt (typed-term-if->then tt to))
         (tte (typed-term-if->else tt to))
         ((typed-term rttc) (term-rectify ttc options state))
         ((typed-term rttt) (term-rectify ttt options state))
         ((typed-term rtte) (term-rectify tte options state)))
      (make-typed-term :term `(if ,rttc.term ,rttt.term ,rtte.term)
                       :path-cond tt.path-cond
                       :judgements tt.judgements)))

  (define fncall-rectify ((tterm typed-term-p)
                          (options type-options-p)
                          state)
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'fncallp))
    :returns (new-tt (and (typed-term-p new-tt)
                          (good-typed-term-p new-tt)))
    :measure (list (acl2-count (typed-term->term tterm))
                   0)
    (b* ((tterm (typed-term-fix tterm))
         (options (type-options-fix options))
         ((unless (mbt (and (good-typed-term-p tterm)
                            (equal (typed-term->kind tterm) 'fncallp))))
          (make-typed-term))
         ((typed-term tt) tterm)
         ((type-options to) options)
         ((typed-term-list tta) (typed-term-fncall->actuals tt to))
         ((cons fn actuals) tt.term)
         (conspair (assoc-equal fn to.functions))
         ((unless conspair)
          (prog2$
           (er hard? 'term-rectify=>fncall-rectify
               "There exists no function description for function ~p0. ~%" fn)
           (make-typed-term)))
         (fn-description (cdr conspair))
         ((mv & & rectify-thms) ;; TODO
          (returns-judgement fn actuals actuals tta.judgements tta.judgements
                             fn-description tta.path-cond to.supertype ''t nil
                             state)))
      (new-tt (rectify tt rectify-thms state))))

(define term-rectify ((tterm typed-term-p)
                      (options type-options-p)
                      state)
  :guard (good-typd-term-p tterm)
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt)))
  :measure (list (acl2-count (typed-term->term tterm)) 1)
  (b* ((tterm (typed-term-fix tterm))
       ((unless (mbt (good-typed-term-p tterm)))
        (make-typed-term))
       ((if (or (equal (typed-term->kind tterm) 'variablep)
                (equal (typed-term->kind tterm) 'quotep)))
        tterm)
       ((if (equal (typed-term->kind tterm) 'lambdap))
        (lambda-rectify tterm options state))
       ((if (equal (typed-term->kind tterm) 'ifp))
        (if-rectify tterm options state)))
    (fncall-rectify tterm options state)))

(define term-list-rectify ((tterm-lst typed-term-list-p)
                           (options type-options-p)
                           state)
  :guard (good-typed-term-list-p tterm-lst)
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl)))
  :measure (list (acl2-count (typed-term-list->term-lst tterm-lst)) 1)
  (b* ((tterm-lst (typed-term-list-fix tterm-lst))
       ((unless (typed-term-list-consp tterm-lst)) tterm-lst))
    (typed-term-list->cons (term-rectify
                            (typed-term->list-car tterm-lst options)
                            options state)
                           (term-list-rectify
                            (typed-term->list-cdr tterm-lst options)
                            options state)
                           options)))
)

(define term-rectify-fn ((cl pseudo-term-listp)
                         (smtlink-hint t)
                         state)
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint))
        (list cl))
       ((smtlink-hint h) smtlink-hint)
       (goal (disjoin cl))
       ((mv err judges original-goal)
        (case-match goal
          (('implies judges original-goal)
           (mv nil judges original-goal))
          (& (mv nil nil nil))))
       ((if err)
        (er hard? 'term-rectify=>term-rectify-fn
            "Theorem should be a implies from a judgement to a goal.~%"))
       (options (construct-type-options smtlink-hint))
       (rectified-tterm (term-rectify (make-typed-term :term original-goal
                                                       :path-cond ''t
                                                       :judgements judges)
                                      options state))
       (new-cl (typed-term->term rectified-tterm))
       (next-cp (cdr (assoc-equal 'term-rectify *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',h state)))
       (hinted-goal `((hint-please ',the-hint) ,new-cl)))
    (list hinted-goal)))

(define term-rectify-cp ((cl pseudo-term-listp)
                          (hints t)
                          state)
  (b* ((decorated-clause (term-rectify-fn cl hints state)))
    (value decorated-clause)))

(local (in-theory (enable term-rectify-cp term-rectify-fn)))

(skip-proofs
(defthm correctness-of-term-rectify-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (term-rectify-cp cl hint state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :rule-classes :clause-processor)
)
