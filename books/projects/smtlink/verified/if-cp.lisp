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
(include-book "clause-processors/join-thms" :dir :system)
(include-book "ordinals/lexicographic-ordering" :dir :system)

(include-book "../verified/pseudo-lambda-lemmas")
(include-book "../verified/hint-please")
(include-book "../verified/hint-interface")
(include-book "../verified/computed-hints")
(include-book "../verified/expand-cp")

(set-state-ok t)

(acl2::defevaluator-fast ifev ifev-lst
                         ((if a b c) (equal a b) (not a)
                          (hint-please hint))
                         :namedp t)
(def-join-thms ifev)

(defines simplify-if
  :well-founded-relation l<
  :flag-local nil
  :flag-defthm-macro defthm-simplify-if
  :verify-guards nil
  :hints (("Goal" :in-theory (disable symbol-listp
                                      acl2::symbol-listp-of-cdr-when-symbol-listp
                                      acl2::symbolp-of-car-when-symbol-listp)))
  :returns-hints (("Goal" :in-theory (disable acl2::pseudo-term-listp-of-cons)))

  (define simplify-if-list ((term-lst pseudo-term-listp))
    :returns (new-term-lst pseudo-term-listp)
    :measure (acl2-count (pseudo-term-list-fix term-lst))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         ((unless (consp term-lst)) term-lst)
         ((cons first rest) term-lst)
         (first-term (simplify-if first)))
      (cons first-term
            (simplify-if-list rest))))

  (define simplify-if ((term pseudo-termp))
    :returns (new-term pseudo-termp)
    :measure (acl2-count (pseudo-term-fix term))
    (b* ((term (pseudo-term-fix term))
         ;; If first term is a symbolp or is quoted, return the current facts
         ((if (or (acl2::variablep term) (acl2::fquotep term))) term)
         ;; The first term is now a function call:
         ;; Cons the function call and function actuals out of term
         ((cons fn-call fn-actuals) term)
         ;; If fn-call is a pseudo-lambdap, this shouldn't happen,
         ((if (pseudo-lambdap fn-call))
          (prog2$
           (er hard? 'if-cp=>simplify-if "There's a lambda in the term,
    wat?~%")
           term))
         ;; If fn-call is neither a lambda expression nor a function call
         ((unless (mbt (symbolp fn-call))) nil)

         ;; -----------------------------------------------------------
         ;; Now the term is a function call
         ;; We only care when it is an if
         ((unless (equal fn-call 'if))
          (cons fn-call (simplify-if-list fn-actuals)))
         ((unless (and (consp fn-actuals)
                       (consp (cdr fn-actuals))
                       (consp (cddr fn-actuals))
                       (null (cdddr fn-actuals))))
          (prog2$
           (er hard? 'if-cp=>simplify-if "If wrong: ~q0" term)
           term))
         (condition (simplify-if (car fn-actuals)))
         (then (simplify-if (cadr fn-actuals)))
         (else (simplify-if (caddr fn-actuals)))
         (new-term
          (cond ((equal condition ''t) then)
                ((equal condition ''nil) else)
                ((and (equal then ''t) (equal else ''t)) ''t)
                ((and (equal then ''t) (equal else ''nil))
                 `(not (equal ,condition 'nil)))
                ((and (equal then ''nil) (equal else ''t))
                 `(equal ,condition 'nil))
                ((and (equal then ''nil) (equal else ''nil)) ''nil)
                (t `(if ,condition ,then ,else)))))
      new-term))
  )

(verify-guards simplify-if)

(defthm-simplify-if
  (defthm simplify-if-term
    (implies (and (alistp a)
                  (pseudo-termp term))
             (equal (ifev (simplify-if term) a)
                    (ifev term a)))
    :hints ('(:expand ((simplify-if term))
                      :in-theory (e/d (ifev-of-fncall-args) ())))
    :flag simplify-if)
  (defthm simplify-if-term-lst
    (implies (and (alistp a)
                  (pseudo-term-listp term-lst))
             (equal (ifev-lst (simplify-if-list term-lst) a)
                    (ifev-lst term-lst a)))
    :hints ('(:expand ((simplify-if-list term-lst)
                       (simplify-if-list nil))))
    :flag simplify-if-list))

(define simplify-if-cp ((cl pseudo-term-listp)
                        (hints t))
  (declare (ignore hints))
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* ((cl (pseudo-term-list-fix cl))
       (fixed-clause (simplify-if (disjoin cl))))
    (list (list fixed-clause))))

(local (in-theory (enable simplify-if-cp)))

(defthm correctness-of-simplify-if
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (ifev (conjoin-clauses (simplify-if-cp clause hints))
                      a))
           (ifev (disjoin clause) a))
  :rule-classes :clause-processor)
