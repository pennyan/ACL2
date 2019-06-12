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
;; Meta-extract stuff
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/sublis-var-meaning" :dir :system)

(include-book "pseudo-lambda-lemmas")
(include-book "hint-please")
(include-book "hint-interface")
(include-book "computed-hints")
(include-book "expand-cp")
(include-book "return-type")

(include-book "ordinals/lexicographic-ordering" :dir :system)
(set-state-ok t)

(defsection uninterpreted-fn-cp
  :parents (verified)
  :short "Verified clause-processor for proving return types of uninterpreted
  functions."

  (acl2::defevaluator-fast unev unev-lst
                           ((if a b c) (equal a b) (not a)
                            (cons a b) (binary-+ a b)
                            (typespec-check ts x)
                            (iff a b)
                            (implies a b)
                            (hint-please hint)
                            (return-last x y z)
                            (binary-+ x y))
                           :namedp t)

  (acl2::def-ev-theoremp unev)
  (acl2::def-meta-extract unev unev-lst)
  (acl2::def-unify unev unev-alist)

  (encapsulate ()
    (local
     (defthm type-thm-full-correct-uninterpreted-1
       (implies (not (unev acl2::x acl2::a))
                (not (unev acl2::x (unev-falsify acl2::x))))
       :hints (("Goal"
                :use ((:functional-instance unev-falsify))
                )))
     )

    (local
     (defthm type-thm-full-correct-uninterpreted-2
       (implies
        (unev
         (meta-extract-global-fact+
          (mv-nth 0
                  (unev-meta-extract-global-badguy state))
          (mv-nth 1
                  (unev-meta-extract-global-badguy state))
          state)
         (unev-falsify (meta-extract-global-fact+
                        (mv-nth 0
                                (unev-meta-extract-global-badguy state))
                        (mv-nth 1
                                (unev-meta-extract-global-badguy state))
                        state)))
        (unev
         (meta-extract-global-fact+ acl2::obj acl2::st state)
         (unev-falsify (meta-extract-global-fact+ acl2::obj acl2::st state))))
       :hints (("Goal"
                :use ((:functional-instance unev-meta-extract-global-badguy)))))
     )


    (defthm type-thm-full-correct-uninterpreted
      (implies (and (unev-meta-extract-global-facts)
                    (alistp a)
                    (pseudo-termp term))
               (or (null (type-thm-full term func state))
                   (unev (type-thm-full term func state) a)))
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d (unev-of-fncall-args)
                               (type-thm-full-correct))
               :use ((:functional-instance
                      type-thm-full-correct
                      (rtev unev)
                      (rtev-lst unev-lst)
                      (rtev-alist unev-alist)
                      (rtev-falsify unev-falsify)
                      (rtev-meta-extract-global-badguy
                       unev-meta-extract-global-badguy)))
               )))
    )


  (define fix-thm-meta-extract ((func func-p)
                                state)
    :returns (new-term pseudo-termp)
    (b* ((func (func-fix func))
         (thms (func->meta-extract-thms func))
         ((mv ok type-fix-when-type)
          (case-match thms
            ((& type-fix-when-type)
             (mv t type-fix-when-type))
            (& (mv nil nil))))
         ((unless ok)
          (er hard? 'uninterpreted-fn-cp=>fix-thm-meta-extract "Smtlink need two theorems
 to justify the proof of return types of uninterpreted functions. Expected
 [type-of-f] and [type-fix-when-type], but got: ~q0" thms))
         (fix-thm (acl2::meta-extract-formula-w type-fix-when-type (w
                                                                    state)))
         ((unless (and (pseudo-termp fix-thm) (not (equal fix-thm ''t))))
          (er hard? 'uninterpreted-fn-cp=>fix-thm-meta-extract "Type theorem
                              type-of-f is not of the expected shape: ~p0 for ~p1~%"
              fix-thm type-fix-when-type)))
      fix-thm))

  (defthm fix-thm-meta-extract-correct
    (implies (and (unev-meta-extract-global-facts)
                  (alistp a))
             (or (null (fix-thm-meta-extract func state))
                 (unev (fix-thm-meta-extract func state) a)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fix-thm-meta-extract
                              unev-of-fncall-args)
                             (pseudo-term-listp
                              pseudo-termp
                              car-cdr-elim
                              w))
             )))

  (define fix-thm-full ((term pseudo-termp)
                        (func func-p)
                        state)
    :returns (new-term pseudo-termp)
    :guard-debug t
    (b* ((term (pseudo-term-fix term))
         (fix-thm (fix-thm-meta-extract func state))
         ((unless fix-thm)
          (er hard? 'uninterpreted-fn-cp=>fix-thm-full
              "Something is wrong with fix-thm-meta-extract."))
         (vars (reverse (acl2::simple-term-vars fix-thm)))
         ((unless (and (consp vars) (null (cdr vars))))
          (er hard? 'uninterpreted-fn-cp=>fix-thm-full
              "Free vars from fix-thm: ~q0" vars)))
      (acl2::substitute-into-term fix-thm (pairlis$ vars (list term)))))

  (defthm fix-thm-full-correct
    (implies (and (unev-meta-extract-global-facts)
                  (alistp a)
                  (pseudo-termp term))
             (or (null (fix-thm-full term func state))
                 (unev (fix-thm-full term func state) a)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (fix-thm-full)
                             (fix-thm-meta-extract-correct))
             :use ((:instance fix-thm-meta-extract-correct
                              (func func)
                              (a (list
                                  (cons (car (reverse
                                              (acl2::simple-term-vars
                                               (fix-thm-meta-extract func state))))
                                        (unev term a))))))
             )))

  (define find-fixer ((term pseudo-termp)
                      (func func-p)
                      state)
    :returns (fixer pseudo-termp)
    (b* ((type-thm (type-thm-full term func state))
         ((unless type-thm)
          (er hard? 'uninterpreted-fn-cp=>find-fixer
              "Something is wrong with type-thm-full."))
         (fix-thm (fix-thm-full term func state))
         ((unless fix-thm)
          (er hard? 'uninterpreted-fn-cp=>find-fixer
              "Something is wrong with fix-thm-full."))
         ((mv ok fixed)
          (case-match fix-thm
            (('implies !type-thm
                       ('equal fixed !term))
             (mv t fixed))
            (& (mv nil nil))))
         ((unless (and ok (pseudo-termp fixed)))
          (er hard? 'uninterpreted-fn-cp=>find-fixer
              "Fixer wrong: ~q0" fixed)))
      fixed))

  (defthm find-fixer-correct
    (implies (and (unev-meta-extract-global-facts)
                  (alistp a)
                  (pseudo-termp term))
             (or (null (find-fixer term func state))
                 (equal (unev (find-fixer term func state) a)
                        (unev term a))))
    :hints (("Goal"
             :in-theory (e/d (find-fixer
                              unev-of-fncall-args)
                             (pseudo-term-listp
                              pseudo-termp
                              car-cdr-elim
                              w
                              fix-thm-full-correct
                              type-thm-full-correct-uninterpreted))
             :use ((:instance fix-thm-full-correct
                              (a a)
                              (term term)
                              (func func))
                   (:instance type-thm-full-correct-uninterpreted
                              (a a)
                              (term term)
                              (func func)))
             )))

  (defines uninterpreted
    :well-founded-relation l<
    :flag-local nil
    :flag-defthm-macro defthm-uninterpreted
    :verify-guards nil

    (define uninterpreted-list ((term-lst pseudo-term-listp)
                                (fn-lst func-alistp)
                                (fty-info fty-info-alist-p)
                                state)
      :returns (new-term-lst pseudo-term-listp)
      :measure (acl2-count (pseudo-term-list-fix term-lst))
      :hints (("Goal" :in-theory (enable pseudo-term-list-fix
                                         pseudo-term-fix)))
      (b* ((term-lst (pseudo-term-list-fix term-lst))
           ((unless (consp term-lst)) term-lst)
           ((cons first rest) term-lst)
           (first-term (uninterpreted first fn-lst fty-info state)))
        (cons first-term
              (uninterpreted-list rest fn-lst fty-info state))))

    (define uninterpreted ((term pseudo-termp)
                           (fn-lst func-alistp)
                           (fty-info fty-info-alist-p)
                           state)
      :returns (new-term pseudo-termp)
      :measure (acl2-count (pseudo-term-fix term))
      (b* ((term (pseudo-term-fix term))
           ;; (fn-lst (func-alist-fix fn-lst))
           ;; If first term is a symbolp or is quoted, return the current facts
           ((if (or (acl2::variablep term) (acl2::fquotep term))) term)
           ;; The first term is now a function call:
           ;; Cons the function call and function actuals out of term
           ((cons fn-call fn-actuals) term)
           ;; If fn-call is a pseudo-lambdap, transform the body
           ((if (pseudo-lambdap fn-call))
            (prog2$ (er hard? 'uninterpreted-fn-cp=>uninterpreted "There still
                           exists lambda in the term. Very strange.~%~q0~%" term)
                    term))
           ;; If fn-call is neither a lambda expression nor a function call
           ((unless (mbt (symbolp fn-call))) nil)
           ((if (equal fn-call 'type-hyp)) term)

           ;; -----------------------------------------------------------
           ;; Now the term is a function call
           (basic-function (member-equal fn-call *SMT-basics*))
           (flex? (fncall-of-flextype fn-call fty-info))
           (basic-fix (member-equal fn-call (strip-cdrs *SMT-fixers*)))
           ((if (or basic-function flex? basic-fix))
            (cons fn-call
                  (uninterpreted-list fn-actuals fn-lst fty-info state)))
           ;; fn-call is not a basic function nor a flex function
           (user-defined (assoc-equal fn-call fn-lst))
           ((unless user-defined)
            (prog2$ (er hard? 'uninterpreted-fn-cp=>uninterpreted "User hasn't
defined the uninterpreted function: ~q0" fn-call)
                    term))
           (fixed (find-fixer term (cdr user-defined) state))
           ((mv ok fixer)
            (case-match fixed
              ((fixer (!fn-call . !fn-actuals))
               (mv t fixer))
              (& (mv nil nil))))
           ((unless (and ok (symbolp fixer)
                         (not (equal fixer 'quote))))
            (prog2$ (er hard? 'uninterpreted-fn-cp=>uninterpreted "Fixer wrong: ~q0" fixer)
                    term)))
        (list fixer
              (cons fn-call (uninterpreted-list fn-actuals fn-lst
                                                fty-info state)))))
    )

  (encapsulate ()
    (local
     (defthm symbolp-of-car-of-pseudo-termp
       (implies (and (consp term)
                     (not (pseudo-lambdap (car term)))
                     (pseudo-termp term))
                (symbolp (car term)))
       :hints (("Goal" :in-theory (enable pseudo-lambdap pseudo-termp))))
     )

    (local
     (defthm func-p-of-cdr-of-assoc-equal-of-func-alistp
       (implies (and (func-alistp fn-lst)
                     (assoc-equal (car term) fn-lst))
                (and (consp (assoc-equal (car term) fn-lst))
                     (func-p (cdr (assoc-equal (car term) fn-lst)))))))

    (verify-guards uninterpreted)

    (defthm-uninterpreted
      (defthm uninterpreted-term
        (implies (and (unev-meta-extract-global-facts)
                      (alistp a)
                      (pseudo-termp term))
                 (equal (unev
                         (uninterpreted term fn-lst fty-info state) a)
                        (unev term a)))
        :hints ('(:expand ((uninterpreted term fn-lst fty-info state))
                          :in-theory (e/d (unev-of-fncall-args)
                                          (find-fixer-correct
                                           member-equal
                                           pseudo-term-listp
                                           pseudo-termp
                                           acl2::member-of-cons))
                          :use ((:instance find-fixer-correct
                                           (term term)
                                           (a a)
                                           (func (cdr (assoc-equal (car term) fn-lst)))))))
        :flag uninterpreted)
      (defthm uninterpreted-term-lst
        (implies (and (unev-meta-extract-global-facts)
                      (alistp a)
                      (pseudo-term-listp term-lst))
                 (equal (unev-lst
                         (uninterpreted-list term-lst fn-lst fty-info state)
                         a)
                        (unev-lst term-lst a)))
        :hints ('(:expand ((uninterpreted-list term-lst fn-lst fty-info state)
                           (uninterpreted-list nil fn-lst fty-info state))))
        :flag uninterpreted-list))
    )

  (define uninterpreted-fn ((cl pseudo-term-listp)
                            (smtlink-hint t)
                            state)
    :returns (new-term pseudo-term-list-listp)
    (b* (((unless (pseudo-term-listp cl)) nil)
         ((unless (smtlink-hint-p smtlink-hint)) (list cl))
         ;; generate all fty related stuff
         (flextypes-table (table-alist 'fty::flextypes-table (w state)))
         ((unless (alistp flextypes-table)) (list cl))
         (h1 (generate-fty-info-alist smtlink-hint flextypes-table))
         (h2 (generate-fty-types-top h1 flextypes-table))
         ((smtlink-hint h) h2)
         (fn-lst (make-alist-fn-lst h.functions))
         (new-term (uninterpreted (disjoin cl) fn-lst h.fty-info state))
         (next-cp (if h.custom-p
                      (cdr (assoc-equal 'uninterpreted-custom
                                        *SMT-architecture*))
                    (cdr (assoc-equal 'uninterpreted *SMT-architecture*))))
         ((if (null next-cp)) (list cl))
         (the-hint
          `(:clause-processor (,next-cp clause ',h state)))
         (hinted-goal `((hint-please ',the-hint) ,new-term)))
      (list hinted-goal)))

  (define uninterpreted-fn-cp ((cl pseudo-term-listp)
                               (hints t)
                               state)
    (b* ((fixed-clause (uninterpreted-fn cl hints state)))
      (value fixed-clause)))

  (local (in-theory (enable uninterpreted-fn-cp uninterpreted-fn)))

  (defthm uninterpreted-fn-correct
    (implies (and (unev-meta-extract-global-facts)
                  (pseudo-term-listp clause)
                  (alistp a)
                  (unev (conjoin-clauses
                         (acl2::clauses-result
                          (uninterpreted-fn-cp clause hints state)))
                        a))
             (unev (disjoin clause) a))
    :rule-classes :clause-processor)
  )
