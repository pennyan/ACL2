;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (July 6th 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "hint-please")
(include-book "hint-interface")
(include-book "extractor")
(include-book "type-hyp")
(include-book "computed-hints")

(defsection type-extract-cp
  :parents (verified)
  :short "Verified clause-processor for extracting type declarations"

  ;; -----------------------------------------------------------------
  ;;       Define evaluators

  (defevaluator ev-extract ev-lst-extract
    ((not x) (if x y z) (implies x y)
     (hint-please hint)))

  (def-join-thms ev-extract)

  ;; -----------------------------------------------------------------
  ;; Defines the clause-processor for extracting type declarations
  ;; (type-hyp (list T1 ... Tn)) => G/type == Q3
  ;; Q3 => G

  (define type-extract-helper ((cl pseudo-term-listp)
                               (smtlink-hint smtlink-hint-p)
                               state)
    :mode :program ;; because of translate-cmp
    ;; :returns (new-hint smtlink-hint-p)
    (b* ((cl (pseudo-term-list-fix cl))
         (smtlink-hint (smtlink-hint-fix smtlink-hint))
         ((smtlink-hint h) smtlink-hint)
         (G (disjoin cl))
         ((mv type-decl-list G/type)
          (SMT-extract G h.fty-info))
         ((mv err type-decl-list-translated)
          (acl2::translate-cmp `(list ,@type-decl-list) t t nil
                               'type-extract-cp->type-extract-helper
                               (w state) (acl2::default-state-vars t)))
         ((when err)
          (er hard? 'type-extract-cp->type-extract-helper "Error ~
    translating form: ~@0" `(list ,@type-decl-list))))
      (change-smtlink-hint h
                           :expanded-G/type G/type
                           :type-decl-list type-decl-list-translated))
    )

  (define type-extract-fn ((cl pseudo-term-listp)
                           (smtlink-hint t))
    :returns (subgoal-lst pseudo-term-list-listp)
    (b* (((unless (pseudo-term-listp cl)) nil)
         ((unless (smtlink-hint-p smtlink-hint))
          (list (remove-hint-please cl)))
         ((smtlink-hint h) smtlink-hint)
         (cl (remove-hint-please cl))
         (G (disjoin cl))
         (type-decl-list h.type-decl-list)
         (G/type h.expanded-G/type)
         (next-cp (cdr (assoc-equal 'type-extract *SMT-architecture*)))
         ((if (null next-cp)) (list cl))
         (the-hint
          `(:clause-processor (,next-cp clause ',h)))
         (cl0 `((hint-please ',the-hint)
                (not (type-hyp (hide ,type-decl-list) ':type))
                ,G/type))
         (type-hint (smtlink-hint->type-hint h))
         (merged-in-theory (treat-in-theory-hint
                            '(hint-please type-hyp)
                            type-hint))
         (more-type-hint (treat-expand-hint '((:free (x) (hide x)))
                                            merged-in-theory))
         (cl1 `((hint-please ',more-type-hint)
                (not (implies (type-hyp (hide ,type-decl-list) ':type)
                              ,G/type))
                ,G)))
      `(,cl0 ,cl1)))

  (defmacro type-extract-cp (clause hint)
    `(type-extract-fn clause
                      (type-extract-helper (remove-hint-please ,clause) ,hint state)))

  ;; proving correctness of the type-extract clause processor
  (local (in-theory (enable type-extract-fn type-hyp hint-please hide)))

  (defthm correctness-of-remove-hint-please-with-ev-extract
    (implies (and (pseudo-term-listp cl)
                  (alistp b))
             (iff (ev-extract (disjoin (remove-hint-please cl)) b)
                  (ev-extract (disjoin cl) b)))
    :hints (("Goal"
             :in-theory (enable hint-please remove-hint-please) )))

  (defthm correctness-of-type-extract-cp
    (implies (and (pseudo-term-listp cl)
                  (alistp b)
                  (ev-extract
                   (conjoin-clauses (type-extract-fn cl smtlink-hint))
                   b))
             (ev-extract (disjoin cl) b))
    :rule-classes :clause-processor)
  )
