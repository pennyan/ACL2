;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 18th 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "clause-processors/just-expand" :dir :system)

;; Include SMT books
(include-book "hint-interface")

;; taken from clause-processors/just-expand
(local
 (defthm expev-of-disjoin
   (iff (acl2::expev (disjoin x) a)
        (acl2::or-list (acl2::expev-lst x a)))
   :hints(("Goal" :in-theory (enable acl2::or-list len)
           :induct (len x))))
 )

(defsection expand-cp

  (define expand-cp ((clause pseudo-term-listp) (smt-hint t)
                     (state t))
    :returns (mv (not-okp)
                 (subgoal-lst pseudo-term-list-listp))
    (b* ((clause (pseudo-term-list-fix clause))
         ;; (clause (remove-hint-please clause))
         ((unless (smtlink-hint-p smt-hint))
          (mv "bad smt-hints" nil))
         ((smtlink-hint h) smt-hint)
         (hints (strip-cars h.expanded-fn-lst))
         ((unless (acl2::just-exp-hints-okp hints))
          (mv "bad expand hints" nil))
         (clause
          (acl2::expand-with-hints-list clause hints nil (w state)))
         ;; need to add hint-please
         ;; (cp-hint `(:clause-processor (smt-verified-cp clause ',h state)))
         ;; (subgoal-lst (cons `(hint-please ',h 'expand-cp) clause))
         )
      (mv nil (list clause))))

  (local (in-theory (e/d (expand-cp
                          acl2::or-list
                          acl2::just-exp-hints-okp))))

  (defthm expand-cp-correct
    (implies (and (acl2::expev-meta-extract-global-facts)
                  (pseudo-term-listp clause)
                  (alistp a)
                  (acl2::expev-theoremp
                   (conjoin-clauses
                    (acl2::clauses-result (expand-cp clause hints state)))))
             (acl2::expev (disjoin clause) a))
    :hints (("goal" :do-not-induct t
             :use ((:instance acl2::expev-falsify
                              (x (disjoin (car (mv-nth 1 (expand-cp clause
                                                                    hints
                                                                    state)))))
                              (a a)))))
    :rule-classes :clause-processor)
  )

