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

(include-book "ordinals/lexicographic-ordering" :dir :system)
(set-state-ok t)

(acl2::defevaluator-fast unev unev-lst
                         ((if a b c) (equal a b) (not a)
                          (cons a b) (binary-+ a b)
                          (typespec-check ts x)
                          (iff a b)
                          (implies a b)
                          (hint-please hint)
                          (return-last x y z))
                         :namedp t)

(acl2::def-ev-theoremp unev)
(acl2::def-meta-extract unev unev-lst)
(acl2::def-unify unev unev-alist)

(local
 (defthm unev-of-disjoin
   (iff (unev (disjoin clause) a)
        (acl2::or-list (unev-lst clause a)))
   :hints(("Goal" :in-theory (enable acl2::or-list len)
           :induct (len clause)))))

(define find-fixer ((term pseudo-termp)
                    (func func-p)
                    state)
  :returns (the-fixer symbolp)
  :guard (and (consp term)
              (symbolp (car term)))
  :guard-debug t
  (b* ((term (pseudo-term-fix term))
       (func (func-fix func))
       (thms (func->meta-extract-thms func))
       ((unless (and (consp thms)
                     (car thms)
                     (consp (cdr thms))
                     (cadr thms)
                     (null (cddr thms))))
        (er hard? 'uninterpreted-fn-cp=>find-fixer "Smtlink need two theorems
 to justify the proof of return types of uninterpreted functions. Expected
 [type-of-f] and [type-fix-when-type], but got: ~q0" thms))
       ((list type-of-f type-fix-when-type) thms)
       (type-thm (acl2::meta-extract-formula-w type-of-f (w state)))
       ((unless (and (consp type-thm)
                     (pseudo-lambdap (car type-thm))
                     (pseudo-term-listp (cdr type-thm))))
        (er hard? 'uninterpreted-fn-cp=>find-fixer "Type theorem type-of-f is
 not of the expected shape: ~q0" type-thm))
       ((cons fn fn-actuals) type-thm)
       (type-thm-w/o-lambda (lambda-substitution fn fn-actuals))
       ((mv ok typep fn-call)
        (case-match type-thm-w/o-lambda
          ((typep fn-call)
           (mv t typep fn-call))
          (& (mv nil nil nil))))
       ((unless (and ok (pseudo-termp fn-call) (symbolp typep)))
        (er hard? 'uninterpreted-fn-cp=>find-fixer "Type theorem after
 substitution does not match expectation: ~q0" type-thm-w/o-lambda))
       ((mv match-ok &)
        (acl2::simple-one-way-unify fn-call term nil))
       ((unless match-ok)
        (er hard? 'uninterpreted-fn-cp=>find-fixer "Simple-one-way-unify
 failed: ~p0 and p1~%" fn-call term))
       (fix-thm (acl2::meta-extract-formula-w type-fix-when-type (w state)))
       ((unless (pseudo-termp fix-thm))
        (er hard? 'uninterpreted-fn-cp=>find-fixer "Fix theorem is not a pseudo-termp: ~q0" fix-thm))
       (formals (all-vars fix-thm))
       ((unless (and (consp formals) (symbolp (car formals))
                     (null (cdr formals))))
        (er hard? 'uninterpreted-fn-cp=>find-fixer "Free vars from the fix
                    theorem do ~p0 not match expectation: ~p1~%" fix-thm
                    formals))
       (fix-thm-substituted
        (acl2::substitute-into-term fix-thm
                                    (pairlis$ formals (list term))))
       ((mv ok the-fixer)
        (case-match fix-thm-substituted
          (('implies (!typep !fn-call)
                     ('equal (the-fixer !fn-call) !fn-call))
           (mv t the-fixer))
          (& (mv nil nil))))
       ((unless (and ok (symbolp the-fixer)))
        (er hard? 'uninterpreted-fn-cp=>find-fixer "Fixer theorem doesn't match expectation" fix-thm)))
    the-fixer))

(skip-proofs
(defthm find-fixer-correct
  (implies (and (unev-meta-extract-global-facts)
                (alistp a)
                (pseudo-termp term)
                (consp term)
                (symbolp (car term)))
           (or (null (find-fixer term func state))
               (equal (unev (cons (find-fixer term func state)
                                  (cons term nil))
                            a)
                      (unev term a))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (find-fixer
                            unev-of-fncall-args)
                           (pseudo-term-listp
                            pseudo-termp
                            car-cdr-elim))
           ))))

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
         ((if (pseudo-lambdap fn-call)) term)
         ;; If fn-call is neither a lambda expression nor a function call
         ((unless (mbt (symbolp fn-call))) nil)

         ;; -----------------------------------------------------------
         ;; Now the term is a function call
         (basic-function (member-equal fn-call *SMT-basics*))
         (flex? (fncall-of-flextype fn-call fty-info))
         ((if (or basic-function flex?)) term)
         ;; fn-call is not a basic function nor a flex function
         (user-defined (assoc-equal fn-call fn-lst))
         ((unless user-defined) term)
         (fixer (find-fixer term (cdr user-defined) state))
         ((unless (and fixer (not (equal fixer 'quote)))) term))
      (cons fixer (cons (cons fn-call (uninterpreted-list fn-actuals fn-lst
                                                          fty-info state))
                        nil))))
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
                                        (find-fixer-correct))
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

(define uninterpreted-cp ((cl pseudo-term-listp)
                          (hints t)
                          state)
  (b* ((fixed-clause (uninterpreted-fn cl hints state)))
    (value fixed-clause)))

(local (in-theory (enable uninterpreted-cp uninterpreted-fn)))

(defthm uninterpreted-fn-correct
  (implies (and (unev-meta-extract-global-facts)
                (pseudo-term-listp clause)
                (alistp a)
                (unev (conjoin-clauses
                       (acl2::clauses-result
                        (uninterpreted-cp clause hints state)))
                      a))
           (unev (disjoin clause) a))
  :rule-classes :clause-processor)
