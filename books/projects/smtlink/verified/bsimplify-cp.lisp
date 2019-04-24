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
                          (consp a)
                          (hint-please hint))
                         :namedp t)
(def-join-thms ifev)

(define bsimplify-not ((fn-actuals pseudo-term-listp))
  :returns (new-term pseudo-termp)
  (b* ((fn-actuals (pseudo-term-list-fix fn-actuals))
       (term `(not ,@fn-actuals))
       (new-term
        (case-match term
          (('not ''t) ''nil)
          (('not ''nil) ''t)
          (('not ('not ('not x))) `(not ,x))
          (('not ('not ('consp x))) `(consp ,x))
          (('not ('not ('equal x y))) `(equal ,x ,y))
          (& term))))
    new-term))

(defthm bsimplify-not-correct
  (implies (and (alistp a)
                (pseudo-term-listp fn-actuals))
           (equal (ifev (bsimplify-not fn-actuals) a)
                  (ifev `(not ,@fn-actuals) a)))
  :hints (("Goal" :in-theory (enable bsimplify-not))))

(define bsimplify-if ((fn-actuals pseudo-term-listp))
  :returns (new-term pseudo-termp)
  (b* ((fn-actuals (pseudo-term-list-fix fn-actuals))
       (term `(if ,@fn-actuals))
       (new-term
        (case-match term
          (('if ''t then &) then)
          (('if ''nil & else) else)
          (('if & a a) a)
          (('if a a ''nil) a)
          (('if ('not x) ''t ''nil) `(not ,x))
          (('if ('not x) ''t ''nil) `(not ,x))
          (('if ('equal x y) ''t ''nil) `(equal ,x ,y))
          (('if ('consp x) ''t ''nil) `(consp ,x))
          (('if ('not ('not x)) ''nil ''t) `(not ,x))
          (('if ('not ('equal x y)) ''nil ''t) `(equal ,x ,y))
          (('if ('not ('consp x)) ''nil ''t) `(consp ,x))
          (('if x ''nil ''t) `(not ,x))
          (('if x ''t ''nil) `(not (equal ,x 'nil)))
          (('if ('not x) then else) `(if ,x ,else ,then))
          (& term))))
    new-term))

(defthm bsimplify-if-correct
  (implies (and (alistp a)
                (pseudo-term-listp fn-actuals))
           (equal (ifev (bsimplify-if fn-actuals) a)
                  (ifev `(if ,@fn-actuals) a)))
  :hints (("Goal" :in-theory (enable bsimplify-if))))

(define bsimplify-equal ((fn-actuals pseudo-term-listp))
  :returns (new-term pseudo-termp)
  :ignore-ok t
  (b* ((fn-actuals (pseudo-term-list-fix fn-actuals))
       (term `(equal ,@fn-actuals))
       (new-term
        (case-match term
          (('equal a a) ''t)
          (('equal a ''nil) `(not ,a))
          (('equal ''nil b) `(not ,b))
          ;; (equal a ''t) when booleanp(a) -> a
          ;; (equal ''t a) when booleanp(a) -> a
          (('equal ('not x) ''t) `(not ,x))
          (('equal ''t ('not x)) `(not ,x))
          (('equal ('equal x y) ''t) `(equal ,x ,y))
          (('equal ''t ('equal x y)) `(equal ,x ,y))
          (('equal ('consp x) ''t) `(consp ,x))
          (('equal ''t ('consp x)) `(consp ,x))
          (& term)))
       )
    new-term))

(defthm bsimplify-equal-correct
  (implies (and (alistp a)
                (pseudo-term-listp fn-actuals))
           (equal (ifev (bsimplify-equal fn-actuals) a)
                  (ifev `(equal ,@fn-actuals) a)))
  :hints (("Goal" :in-theory (enable bsimplify-equal))))

(defines bsimplify
  :well-founded-relation l<
  :flag-local nil
  :flag-defthm-macro defthm-bsimplify
  :verify-guards nil
  :hints (("Goal"
           :in-theory (disable symbol-listp
                               acl2::symbol-listp-of-cdr-when-symbol-listp
                               acl2::symbolp-of-car-when-symbol-listp)))
  :returns-hints (("Goal"
                   :in-theory (disable acl2::pseudo-term-listp-of-cons)))

  (define bsimplify-list ((term-lst pseudo-term-listp))
    :returns (new-term-lst pseudo-term-listp)
    :measure (acl2-count (pseudo-term-list-fix term-lst))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         ((unless (consp term-lst)) term-lst)
         ((cons first rest) term-lst)
         (first-term (bsimplify first)))
      (cons first-term
            (bsimplify-list rest))))

  (define bsimplify ((term pseudo-termp))
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
          (prog2$ (er hard? 'bsimplify-cp=>bsimplify
                      "There's a lambda in the term, wat?~%")
                  term))
         ;; If fn-call is neither a lambda expression nor a function call
         ((unless (mbt (symbolp fn-call))) nil)
         ;; -----------------------------------------------------------
         ;; Now the term is a function call
         ;; We only care when it is an if
         (simplified-fn-actuals (bsimplify-list fn-actuals))
         (new-term
          (cond ((equal fn-call 'equal)
                 (bsimplify-equal simplified-fn-actuals))
                ((equal fn-call 'not)
                 (bsimplify-not simplified-fn-actuals))
                ((equal fn-call 'if)
                 (bsimplify-if simplified-fn-actuals))
                (t (cons fn-call simplified-fn-actuals))))
         (- (cw "term: ~q0" term))
         (- (cw "new-term: ~q0" new-term)))
      new-term))
  )

(verify-guards bsimplify)

(defthm-bsimplify
  (defthm bsimplify-term
    (implies (and (alistp a)
                  (pseudo-termp term))
             (equal (ifev (bsimplify term) a)
                    (ifev term a)))
    :hints ('(:expand ((bsimplify term))
                      :in-theory (e/d (ifev-of-fncall-args) ())))
    :flag bsimplify)
  (defthm bsimplify-term-lst
    (implies (and (alistp a)
                  (pseudo-term-listp term-lst))
             (equal (ifev-lst (bsimplify-list term-lst) a)
                    (ifev-lst term-lst a)))
    :hints ('(:expand ((bsimplify-list term-lst)
                       (bsimplify-list nil))))
    :flag bsimplify-list))

(define bsimplify-cp ((cl pseudo-term-listp)
                      (hints t))
  (declare (ignore hints))
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* ((cl (pseudo-term-list-fix cl))
       (fixed-clause (bsimplify (disjoin cl)))
       (- (cw "after if-cp: ~q0" fixed-clause))
       )
    (list `((hint-please
             '(:in-theory (enable magic-fix
                                  hint-please
                                  type-hyp)
                          :expand ((:free (x) (hide x)))))
            ,fixed-clause))))

(local (in-theory (enable bsimplify-cp)))

(defthm correctness-of-bsimplify
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (ifev (conjoin-clauses (bsimplify-cp clause hints))
                      a))
           (ifev (disjoin clause) a))
  :rule-classes :clause-processor)
