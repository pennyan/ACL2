(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
;; for symbol-fix
(include-book "centaur/fty/basetypes" :dir :system)
;; for symbol-list-fix
(include-book "centaur/fty/baselists" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)
;; To be compatible with Arithmetic books
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
;; Meta-extract stuff
(include-book "clause-processors/just-expand" :dir :system)

;; Include SMT books
(include-book "pseudo-lambda-lemmas")
(include-book "hint-interface")
(include-book "extractor")
(include-book "basics")
(include-book "hint-please")
(include-book "computed-hints")

(set-state-ok t)

(defsection function-expansion
  :parents (verified)
  :short "Function expansion"

(acl2::defevaluator-fast expev expev-lst
                         ((if a b c) (equal a b) (not a)
                          (cons a b) (binary-+ a b)
                          (typespec-check ts x)
                          (iff a b)
                          (implies a b)
                          (hint-please hint)
                          (return-last x y z))
                         :namedp t)

(acl2::def-ev-theoremp expev)
(acl2::def-meta-extract expev expev-lst)
(acl2::def-unify expev expev-alist)

(defalist sym-nat-alist
  :key-type symbol
  :val-type natp
  :pred sym-nat-alistp
  :true-listp t)

(local
 (defthm consp-of-sym-nat-alist-fix
   (implies (consp (sym-nat-alist-fix x)) (consp x))
   :hints (("Goal" :in-theory (enable sym-nat-alist-fix))))
 )

(local
 (defthm len-of-sym-nat-alist-fix-<
   (> (1+ (len x)) (len (sym-nat-alist-fix x)))
   :hints (("Goal" :in-theory (enable sym-nat-alist-fix))))
 )

(local
 (defthm natp-of-cdar-sym-nat-alist-fix
   (implies (consp (sym-nat-alist-fix x))
            (natp (cdar (sym-nat-alist-fix x))))
   :hints (("Goal" :in-theory (enable sym-nat-alist-fix))))
 )

(define update-fn-lvls ((fn symbolp) (fn-lvls sym-nat-alistp))
  :returns (updated-fn-lvls sym-nat-alistp)
  :measure (len fn-lvls)
  :hints (("Goal" :in-theory (enable sym-nat-alist-fix)))
  (b* ((fn (symbol-fix fn))
       (fn-lvls (sym-nat-alist-fix fn-lvls))
       ((unless (consp fn-lvls)) nil)
       ((cons first rest) fn-lvls)
       ((cons this-fn this-lvl) first)
       ((unless (equal fn this-fn))
        (cons (cons this-fn this-lvl)
              (update-fn-lvls fn rest))))
    (if (zp this-lvl)
        (cons (cons this-fn 0) rest)
      (cons (cons this-fn (1- this-lvl)) rest)))
  ///
  (more-returns
   (updated-fn-lvls
    (implies (and (symbolp fn)
                  (sym-nat-alistp fn-lvls)
                  (consp fn-lvls)
                  (assoc-equal fn fn-lvls)
                  (not (equal (cdr (assoc-equal fn fn-lvls)) 0)))
             (< (cdr (assoc fn updated-fn-lvls))
                (cdr (assoc fn fn-lvls))))
    :name updated-fn-lvls-decrease))
  )


;; val-type can be a list of pseudo-termp
;; This will give us two benefits: multiple facts and when it's nil,
;; fact-finder fails to find a fact.
(defalist fact-alist
  :key-type pseudo-termp
  :val-type pseudo-termp
  :pred fact-alistp
  :short "Value is the equivalence term about Key term."
  :true-listp t)

(defprod ex-args
  :parents (function-expansion)
  :short "Argument list for function expand"
  ((fn-lvls sym-nat-alistp "Levels to expand each functions to."
            :default nil)
   (fn-lst func-alistp "List of function definitions to use for
      function expansion." :default nil)
   (facts fact-alistp "An alist of current learnt equivalence facts."
          :default nil)
   (fty-info fty-info-alist-p "FTY information." :default nil)
   (wrld-fn-len natp "Number of function definitions in curent world."
                :default 0)))

(local
 (defthm natp-of-sum-lvls-lemma
   (implies (and (consp (sym-nat-alist-fix fn-lvls)) (natp x))
            (natp (+ (cdr (car (sym-nat-alist-fix fn-lvls))) x)))
   :hints (("Goal"
            :in-theory (enable sym-nat-alist-fix)
            :use ((:instance natp-of-cdar-sym-nat-alist-fix)))))
 )

(define sum-lvls ((fn-lvls sym-nat-alistp))
  :returns (sum natp
                :hints (("Goal"
                         :use ((:instance natp-of-sum-lvls-lemma
                                          (x (sum-lvls (cdr (sym-nat-alist-fix fn-lvls)))))))))
  :measure (len fn-lvls)
  :hints (("Goal" :in-theory (enable sym-nat-alist-fix)))
  (b* ((fn-lvls (sym-nat-alist-fix fn-lvls))
       ((unless (consp fn-lvls)) 0)
       ((cons first rest) fn-lvls)
       ((cons & lvl) first))
    (+ lvl (sum-lvls rest)))
  ///
  (defthm sum-lvls-decrease-after-update
    (implies (and (symbolp fn)
                  (sym-nat-alistp fn-lvls)
                  (consp fn-lvls)
                  (assoc-equal fn fn-lvls)
                  (not (equal (cdr (assoc-equal fn fn-lvls)) 0)))
             (< (sum-lvls (update-fn-lvls fn fn-lvls))
                (sum-lvls fn-lvls)))
    :hints (("Goal" :in-theory (enable update-fn-lvls)))))

(encapsulate ()
  (local (defthm alistp-of-pairlis$
           (alistp (acl2::pairlis$ a b))))

  (local (defthm pseudo-term-substp-of-pairlis$-for-pseudo-lambda
           (implies (and (pseudo-term-listp x) (pseudo-lambdap y))
                    (acl2::pseudo-term-substp (pairlis$ (lambda-formals y) x)))))

  (define lambda-substitution ((fn-call pseudo-lambdap)
                               (fn-actuals pseudo-term-listp))
    :guard-hints (("Goal"
                   :in-theory (e/d () (alistp-of-pairlis$
                                       acl2::true-listp-when-symbol-listp))
                   :use ((:instance acl2::true-listp-when-symbol-listp
                                    (acl2::x (cadr fn-call)))
                         (:instance alistp-of-pairlis$
                                    (a (cadr fn-call))
                                    (b fn-actuals)))))
    :returns (subst-term
              pseudo-termp
              :hints (("Goal"
                       :in-theory (e/d ()
                                       (pseudo-term-substp-of-pairlis$-for-pseudo-lambda
                                        acl2::return-type-of-substitute-into-term.xx))
                       :use ((:instance
                              pseudo-term-substp-of-pairlis$-for-pseudo-lambda
                              (x fn-actuals)
                              (y fn-call))
                             (:instance
                              acl2::return-type-of-substitute-into-term.xx
                              (x (lambda-body (pseudo-lambda-fix fn-call)))
                              (al (pairlis$ (lambda-formals
                                             (pseudo-lambda-fix fn-call))
                                            (pseudo-term-list-fix fn-actuals))))))))
    (b* ((fn-call (pseudo-lambda-fix fn-call))
         (fn-actuals (pseudo-term-list-fix fn-actuals))
         (formals (lambda-formals fn-call))
         (body (lambda-body fn-call)))
      (acl2::substitute-into-term body (pairlis$ formals fn-actuals)))))

(define function-substitution ((term pseudo-termp)
                               state)
  :returns (subst-term
            pseudo-termp
            :hints (("Goal"
                     :in-theory (e/d ()
                                     (pseudo-termp
                                      pseudo-term-listp
                                      acl2::return-type-of-substitute-into-term.xx
                                      acl2::return-type-of-simple-one-way-unify.a))
                     :use ((:instance
                            acl2::return-type-of-simple-one-way-unify.a
                            (pat (cadr (acl2::meta-extract-formula-w
                                        (symbol-fix fn-call)
                                        (cdr (assoc-equal 'acl2::current-acl2-world
                                                          (nth 2 state))))))
                            (term (pseudo-term-fix term))
                            (alist nil))))))
  (b* ((term (pseudo-term-fix term))
       ((unless (and (not (acl2::variablep term))
                     (not (acl2::fquotep term))
                     (symbolp (car term))))
        (prog2$
         (er hard? 'expand-cp=>function-substitution "expand-cp: fn-call is nil
                               or 'quote.")
         nil))
       ((cons fn-call &) term)
       (formula (acl2::meta-extract-formula-w fn-call (w state)))
       ((unless (pseudo-termp formula))
        (prog2$
         (er hard? 'expand-cp=>function-substitution "expand-cp: formula got by
       meta-extract is not a pseudo-termp.")
         nil))
       ((mv ok lhs rhs)
        (case-match formula
          (('equal lhs rhs)
           (mv t lhs rhs))
          (& (mv nil nil nil))))
       ((unless (and ok (pseudo-termp lhs)))
        (prog2$ (er hard? 'expand-cp=>function-substitution "expand-cp: formula got by
       meta-extract is not an equality.")
                nil))
       ((mv match-ok subst)
        (acl2::simple-one-way-unify lhs term nil))
       ((unless match-ok)
        (prog2$
         (er hard? 'expand-cp=>function-substitution "expand-cp:
       simple-one-way-unify failed.")
         nil)))
    `(equal ,term ,(acl2::substitute-into-term rhs subst))))

(encapsulate()
(local (in-theory (e/d (function-substitution) (w))))

(defthm function-substitution-correct
  (implies (and (expev-meta-extract-global-facts)
                (pseudo-termp term)
                (alistp a)
                (function-substitution term state))
           (expev (function-substitution term state) a))
  :hints (("Goal"
           :in-theory (e/d ()
                           (expev-meta-extract-formula))
           :use ((:instance
                  expev-meta-extract-formula
                  (name (car term))
                  (st state)
                  (a (expev-alist
                      (mv-nth 1
                              (acl2::simple-one-way-unify
                               (cadr (meta-extract-formula (car term) state))
                               term nil))
                      a))))
           ))
  )
)

(encapsulate ()
  (local
   (defthm type-of-assoc-equal-of-sym-nat-alistp
     (implies (and (sym-nat-alistp x)
                   (symbolp y)
                   (assoc-equal y x))
              (and (symbolp (car (assoc-equal y x)))
                   (natp (cdr (assoc-equal y x))))))
   )

  (define fact-finder ((term pseudo-termp)
                       (expand-args ex-args-p)
                       state)
    :guard (and (not (acl2::variablep term))
                (not (acl2::fquotep term))
                (symbolp (car term))
                (not (assoc-equal term (ex-args->facts expand-args)))
                (not (zp (ex-args->wrld-fn-len expand-args))))
    :guard-hints (("Goal"
                   :in-theory (e/d ()
                                   (type-of-assoc-equal-of-sym-nat-alistp))
                   :use ((:instance type-of-assoc-equal-of-sym-nat-alistp
                                    (x (ex-args->fn-lvls expand-args))
                                    (y (car term))))))
    :returns (mv (new-term pseudo-termp)
                 (new-args ex-args-p))
    :short "Find the definition fact for @('term')"
    :long "<p>Given a pseudo-termp @('term') that is not a @('variablep'), not
a @('fquotep'), nor a @('pseudo-lambdap'), and that it doesn't exist in the
list of facts learnt @('(ex-args->facts expand-args)'), we want to find the
definition fact of that term.</p>
"
    (b* ((term (pseudo-term-fix term))
         (expand-args (ex-args-fix expand-args))
         ((ex-args a) expand-args)
         ((cons fn &) term)
         ;; There are three cases:
         ;; 1. fn is a basic function (including fty functions) -- fn-lvls stays
         ;; the same, nothing is expanded, no fact generated
         ;; For 2 and 3, if fn-lvls is already 0, then do nothing; if fn-lvls is
         ;; not 0, expand.
         ;; 2. fn exists in user-defined fn-lvls -- fn-lvls decrease by 1, fn is
         ;; expanded, one fact generated
         ;; 3. otherwise, fn will be expanded once -- fn-lvls decrease by 1, fn
         ;; is expanded, one fact generated
         (basic-function (member-equal fn *SMT-basics*))
         (flex? (fncall-of-flextype fn a.fty-info))
         ((if (or basic-function flex?))
          (mv nil a))
         (lvl (assoc-equal fn a.fn-lvls))
         (user-defined (assoc-equal fn a.fn-lst))
         ((if (and lvl (zp (cdr lvl)) user-defined)) (mv nil a))
         ((if (and lvl (zp (cdr lvl)) (null user-defined)))
          (prog2$ (er hard? 'expand-cp=>fact-finder "Possibly
                       encountered recursive functions that are not
                       user-defined: ~q0" term)
                  (mv nil a)))
         (fact (function-substitution term state))
         ((if (null fact)) (mv nil a))
         ((if lvl)
          (mv fact
              (make-ex-args :fn-lvls (update-fn-lvls fn a.fn-lvls)
                            :fn-lst a.fn-lst
                            :facts (acons term fact a.facts)
                            :fty-info a.fty-info
                            :wrld-fn-len a.wrld-fn-len))))
      ;; if not in fn-lvls
      (mv fact
          (make-ex-args :fn-lst a.fn-lst
                        :fn-lvls (cons `(,fn . 0) a.fn-lvls)
                        :facts (acons term fact a.facts)
                        :fty-info a.fty-info
                        :wrld-fn-len (1- a.wrld-fn-len))))
    ///
    (more-returns
     (new-args
      (implies
       (and (pseudo-termp term)
            (ex-args-p expand-args)
            (symbolp (car term))
            new-term
            (assoc-equal (car term)
                         (ex-args->fn-lvls expand-args)))
       (and (< (sum-lvls (ex-args->fn-lvls new-args))
               (sum-lvls (ex-args->fn-lvls expand-args)))
            (equal (ex-args->wrld-fn-len new-args)
                   (ex-args->wrld-fn-len expand-args))))
      :hints (("Goal"
               :in-theory (e/d ()
                               (sum-lvls-decrease-after-update))
               :use ((:instance sum-lvls-decrease-after-update
                                (fn (car term))
                                (fn-lvls (ex-args->fn-lvls expand-args))))))
      :name fact-finder-decrease-1)
     (new-args
      (implies
       (and (pseudo-termp term)
            (ex-args-p expand-args)
            (symbolp (car term))
            (not (zp (ex-args->wrld-fn-len expand-args)))
            new-term
            (not (assoc-equal (car term)
                              (ex-args->fn-lvls expand-args))))
       (< (ex-args->wrld-fn-len new-args)
          (ex-args->wrld-fn-len expand-args)))
      :name fact-finder-decrease-2)
     (new-args
      (implies (not new-term)
               (and (equal (ex-args->wrld-fn-len new-args)
                           (ex-args->wrld-fn-len expand-args))
                    (equal (sum-lvls (ex-args->fn-lvls new-args))
                           (sum-lvls (ex-args->fn-lvls expand-args)))))
      :name fact-finder-same-3)
     )
    )
  )

(encapsulate ()
(local
 (defthm acl2-count-of-last-of-consp-decrease
   (implies (consp x)
            (< (acl2-count (pseudo-term-fix (car (last x))))
               (acl2-count x)))
   :hints (("Goal"
            :in-theory (enable pseudo-term-fix)))
   ))

(local
 (defthm symbolp-of-fn-call-of-pseudo-termp
   (implies (and (pseudo-termp x)
                 (consp x)
                 (not (acl2::fquotep x))
                 (not (pseudo-lambdap (car x))))
            (symbolp (car x)))
   :hints (("Goal" :in-theory (enable pseudo-lambdap)))))

(defines transform
  :well-founded-relation l<
  :flag-local nil
  :flag-defthm-macro defthm-transform
  :verify-guards nil

  (define transform-list ((term-lst pseudo-term-listp))
    :returns (new-term-lst pseudo-term-listp)
    :measure (acl2-count (pseudo-term-list-fix term-lst))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         ((unless (consp term-lst)) term-lst)
         ((cons first rest) term-lst)
         (first-term (transform first)))
      (cons first-term
            (transform-list rest))))

  (define transform ((term pseudo-termp))
    :returns (new-term pseudo-termp)
    :measure (acl2-count (pseudo-term-fix term))
    :hints (("Goal"
             :in-theory (e/d ()
                             (acl2-count-of-last-of-consp-decrease))
             :use ((:instance acl2-count-of-last-of-consp-decrease
                              (x (cdr (pseudo-term-fix term)))))))
    (b* ((term (pseudo-term-fix term))
         ;; If first term is a symbolp or is quoted, return the current facts
         ((if (or (acl2::variablep term) (acl2::fquotep term))) term)
         ;; The first term is now a function call:
         ;; Cons the function call and function actuals out of term
         ((cons fn-call fn-actuals) term)
         ;; If fn-call is a pseudo-lambdap, transform the body
         ((if (pseudo-lambdap fn-call))
          (b* (((list 'lambda formal-lst body) fn-call)
               (transformed-body (transform body))
               (transformed-actuals (transform-list fn-actuals))
               ((unless (mbt (equal (len formal-lst)
                                    (len transformed-actuals))))
                nil))
            (cons `(lambda ,formal-lst ,transformed-body)
                  transformed-actuals)))
         ;; If fn-call is neither a lambda expression nor a function call
         ((unless (mbt (symbolp fn-call))) nil)

         ;; -----------------------------------------------------------
         ;; Now the term is a function call
         ((if (and (equal fn-call 'acl2::return-last)
                   (equal (len fn-actuals) 3)))
          (transform (car (last term)))))
      (cons fn-call (transform-list fn-actuals))))
  )

(local
(defthm tranform-list-maintain-length
  (implies (pseudo-term-listp term-lst)
           (equal (len (transform-list term-lst))
                  (len term-lst)))
  :hints (("Goal"
           :expand (transform-list term-lst))))
)

(local
 (defthm pseudo-termp-of-car-of-last-of-return-last
   (implies (and (pseudo-term-listp x)
                 (consp x))
            (pseudo-termp (car (last x))))
   :hints (("Goal"
            :in-theory (enable pseudo-term-listp last)))
   ))

(verify-guards transform)

(defines induction-scheme
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil

  (define induction-scheme-list ((term-lst pseudo-term-listp)
                                 (al))
    (declare (irrelevant al))
    :measure (acl2-count (pseudo-term-list-fix term-lst))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         ((unless (consp term-lst)) term-lst)
         ((cons first rest) term-lst))
      (cons (induction-scheme first al)
            (induction-scheme-list rest al))))

  (define induction-scheme ((term pseudo-termp)
                            (al))
    (declare (irrelevant al))
    :measure (acl2-count (pseudo-term-fix term))
    :hints (("Goal"
             :in-theory (e/d ()
                             (acl2-count-of-last-of-consp-decrease))
             :use ((:instance acl2-count-of-last-of-consp-decrease
                              (x (cdr (pseudo-term-fix term)))))))
    (b* ((term (pseudo-term-fix term))
         ;; If first term is a symbolp or is quoted, return the current facts
         ((if (or (acl2::variablep term) (acl2::fquotep term))) term)
         ;; The first term is now a function call:
         ;; Cons the function call and function actuals out of term
         ((cons fn-call fn-actuals) term)
         ;; If fn-call is a pseudo-lambdap, transform the body
         ((if (pseudo-lambdap fn-call))
          (b* (((list 'lambda formal-lst body) fn-call)
               ;; (transformed-body (transform body))
               ;; (transformed-actuals (transform-list fn-actuals))
               ((unless (mbt (equal (len formal-lst)
                                    (len fn-actuals))))
                nil))
            (cons (induction-scheme body
                                    (pairlis$ formal-lst
                                              (expev-lst fn-actuals al)))
                  (induction-scheme-list fn-actuals al))))
         ;; If fn-call is neither a lambda expression nor a function call
         ((unless (mbt (symbolp fn-call))) nil)

         ;; -----------------------------------------------------------
         ;; Now the term is a function call
         ((if (and (equal fn-call 'acl2::return-last)
                   (equal (len fn-actuals) 3)))
          (induction-scheme (car (last term)) al)))
      (induction-scheme-list fn-actuals al)))
  )

(local
 (defthm induction-scheme-list-maintain-length
   (implies (pseudo-term-listp term-lst)
            (equal (len (induction-scheme-list term-lst al))
                   (len term-lst)))
   :hints (("Goal"
            :expand ((induction-scheme-list term-lst al)
                     (induction-scheme-list nil al)))))
 )

(local
 (defthm cdr-of-transform-list
   (implies (pseudo-term-listp x)
            (equal (transform-list (cdr x))
                   (cdr (transform-list x))))
   :hints (("Goal"
            :expand (transform-list x)))
   ))

(local
 (defthm crock1
   (implies (equal (len x) 1)
            (equal (car (last x))
                   (car x)))
   :hints (("Goal"
            :in-theory (enable last len)))))

(defthm-induction-scheme-flag
  (defthm transform-pseudo-termp
    (implies (and (expev-meta-extract-global-facts)
                  (pseudo-termp term))
             (equal (expev (transform term) a)
                    (expev term a)))
    :hints ('(:expand ((transform term))
                      :in-theory (enable expev-of-fncall-args)))
    :flag induction-scheme)
  (defthm transform-pseudo-term-listp
    (implies (and (expev-meta-extract-global-facts)
                  (pseudo-term-listp term-lst))
             (equal (expev-lst (transform-list term-lst) a)
                    (expev-lst term-lst a)))
    :hints ('(:expand ((transform-list term-lst)
                       (transform-list nil))))
    :flag induction-scheme-list)
  :hints(("Goal" :induct (induction-scheme-flag flag term-lst term a))))

(defines expand
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :flag-defthm-macro defthm-expand

  (define expand-list ((term-lst pseudo-term-listp)
                       (expand-args ex-args-p)
                       state)
    :returns (fact-alst fact-alistp)
    :measure (list (ex-args->wrld-fn-len expand-args)
                   (sum-lvls (ex-args->fn-lvls expand-args))
                   (acl2-count (pseudo-term-list-fix term-lst)))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (expand-args (ex-args-fix expand-args))
         ((ex-args a) expand-args)
         ((unless (consp term-lst)) a.facts)
         ((cons first rest) term-lst)
         (facts-first (expand first a state)))
      (expand-list rest (change-ex-args a :facts facts-first) state)))

  (define expand ((term pseudo-termp)
                  (expand-args ex-args-p)
                  state)
    :returns (fact-alst fact-alistp)
    :measure (list (ex-args->wrld-fn-len expand-args)
                   (sum-lvls (ex-args->fn-lvls expand-args))
                   (acl2-count (pseudo-term-fix term)))
    :hints (("Goal"
             :in-theory (e/d ()
                             (fact-finder-decrease-1
                              fact-finder-decrease-2
                              fact-finder-same-3))
             :use ((:instance fact-finder-decrease-1
                              (term (pseudo-term-fix term))
                              (expand-args (ex-args-fix expand-args)))
                   (:instance fact-finder-decrease-2
                              (term (pseudo-term-fix term))
                              (expand-args (ex-args-fix expand-args)))
                   (:instance fact-finder-same-3
                              (term (pseudo-term-fix term))
                              (expand-args (ex-args-fix expand-args)))
                   (:instance acl2-count-of-last-of-consp-decrease
                              (x (cdr (pseudo-term-fix term))))
                   )))
    (b* ((term (pseudo-term-fix term))
         (expand-args (ex-args-fix expand-args))
         ((ex-args a) expand-args)
         ((if (zp a.wrld-fn-len)) a.facts)
         ;; If first term is a symbolp or is quoted, return the current facts
         ((if (or (acl2::variablep term) (acl2::fquotep term))) a.facts)
         ;; The first term is now a function call:
         ;; Cons the function call and function actuals out of term
         ((cons fn-call fn-actuals) term)
         ;; If fn-call is a pseudo-lambdap, substitute unbounded variables in the
         ;; lambda and recurse to expand the substituted term.
         ;; To ensure termination, wrld-fn-len needs to decrease, this means
         ;; wrld-fn-len should include term size so that it's large enough.
         ((if (pseudo-lambdap fn-call))
          (expand (lambda-substitution fn-call fn-actuals)
                  (change-ex-args a :wrld-fn-len (1- a.wrld-fn-len))
                  state))
         ;; If fn-call is neither a lambda expression nor a function call
         ((unless (mbt (symbolp fn-call))) nil)

         ;; -----------------------------------------------------------
         ;; Now the term is a function call we first test if term already
         ;; exists in facts alist.
         (exists? (assoc-equal term a.facts))
         ;; I can skip the whole subtree because if such a term already exists in
         ;; facts, then it's subterms, subsubterms ... must also exist in the
         ;; facts. This is because we are doing a depth first travesal.
         ((if exists?) a.facts)
         ((mv new-term new-args) (fact-finder term a state))
         ;; new-term being nil meaning there's no fact to prove
         ((unless new-term)
          (expand-list fn-actuals new-args state)))
      (expand new-term new-args state)))
  )

(verify-guards expand)
)

(define initialize-fn-lvls ((fn-lst func-alistp))
  :returns (fn-lvls sym-nat-alistp)
  :measure (len fn-lst)
  :hints (("Goal" :in-theory (enable func-alist-fix)))
  (b* ((fn-lst (func-alist-fix fn-lst))
       ((unless (consp fn-lst)) nil)
       ((cons first rest) fn-lst)
       ((func f) (cdr first)))
    (cons (cons f.name f.expansion-depth) (initialize-fn-lvls rest))))

(define generate-fty-info-alist ((hints smtlink-hint-p)
                                 (flextypes-table alistp))
  :returns (updated-hints smtlink-hint-p)
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       ((unless (alistp flextypes-table)) h)
       (fty-info (generate-fty-info-alist-rec h.fty nil flextypes-table)))
    (change-smtlink-hint h :fty-info fty-info)))

(local
 (defthm crock-for-generate-fty-types-top
   (implies (fty-types-p x)
            (fty-types-p (reverse x)))))

(define generate-fty-types-top ((hints smtlink-hint-p)
                                (flextypes-table alistp))
  :returns (updated-hints smtlink-hint-p)
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       ((unless (alistp flextypes-table)) h)
       ((mv & ordered-acc)
        (generate-fty-type-list h.fty flextypes-table
                                h.fty-info nil nil))
       (fty-types (reverse ordered-acc)))
    (change-smtlink-hint h :fty-types fty-types)))

(define compose-goal ((cl pseudo-term-listp)
                      (to-be-learnt pseudo-term-listp)
                      state)
  :returns (new-goal pseudo-term-listp)
  :measure (len (pseudo-term-list-fix to-be-learnt))
  (b* ((cl (pseudo-term-list-fix cl))
       (to-be-learnt (pseudo-term-list-fix to-be-learnt))
       ((unless (consp to-be-learnt)) cl)
       ((cons first-fact rest-facts) to-be-learnt)
       ((unless (and (not (acl2::variablep first-fact))
                     (not (acl2::fquotep first-fact))
                     (symbolp (car first-fact))))
        cl)
       (learnt-fact (function-substitution first-fact state))
       ((if (null learnt-fact)) cl))
    `((not ,learnt-fact)
      ,@(compose-goal cl rest-facts state))))

(encapsulate ()
(local (in-theory (e/d (compose-goal) ())))

(local
 (defthm expev-of-disjoin
   (iff (expev (disjoin clause) a)
        (acl2::or-list (expev-lst clause a)))
   :hints(("Goal" :in-theory (enable acl2::or-list len)
           :induct (len clause)))))

(defthm compose-goal-correct
  (implies (and (expev-meta-extract-global-facts)
                (pseudo-term-listp clause)
                (alistp a)
                (expev (disjoin
                        (compose-goal clause to-be-learnt state))
                       a))
           (expev (disjoin clause) a))
  :hints (("Goal"
           :in-theory (disable expev-of-disjoin)
           :expand (compose-goal clause to-be-learnt state)
           :use
           ((:instance function-substitution-correct
                       (term (car (pseudo-term-list-fix to-be-learnt)))
                       (a a)
                       (state state)))
           ))
  )

(defthm compose-transformed-goal-correct
  (implies (and (expev-meta-extract-global-facts)
                (pseudo-term-listp clause)
                (alistp a)
                (expev
                 (disjoin
                  (compose-goal (transform-list clause) to-be-learnt state))
                 a))
           (expev (disjoin clause) a)))
)

(encapsulate ()
  (local
   (defthm pseudo-term-listp-of-strip-cars-of-fact-alistp
     (implies (fact-alistp x)
              (pseudo-term-listp (strip-cars x)))))

(define expand-cp-helper ((cl pseudo-term-listp)
                          (smtlink-hint t)
                          state)
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint))
        (list cl))
       ;; generate all fty related stuff
       (flextypes-table (table-alist 'fty::flextypes-table (w state)))
       ((unless (alistp flextypes-table)) (list cl))
       (h1 (generate-fty-info-alist smtlink-hint flextypes-table))
       (h2 (generate-fty-types-top h1 flextypes-table))
       ((smtlink-hint h) h2)
       ;; Make an alist version of fn-lst
       (fn-lst (make-alist-fn-lst h.functions))
       (fn-lvls (initialize-fn-lvls fn-lst))
       (wrld-fn-len h.wrld-fn-len)
       (transformed-cl (transform-list cl))
       ;; Do function expansion
       (facts nil)
       (to-be-learnt
        (with-fast-alists (facts fn-lvls fn-lst)
          (expand (disjoin transformed-cl)
                  (make-ex-args
                   :fn-lvls fn-lvls
                   :fn-lst fn-lst
                   :facts facts
                   :fty-info h.fty-info
                   :wrld-fn-len wrld-fn-len)
                  state)))
       (expanded-goal (compose-goal transformed-cl (strip-cars to-be-learnt) state))
       (next-cp (cdr (assoc-equal 'expand *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',h)))
       (hinted-goal `((hint-please ',the-hint) ,@expanded-goal)))
    (list hinted-goal)))
)

(define expand-cp ((cl pseudo-term-listp)
                   (hints t)
                   state)
  (b* ((expanded-clause (expand-cp-helper cl hints state)))
    (value expanded-clause)))

(local (in-theory (enable expand-cp expand-cp-helper)))

(defthm correctness-of-expand-cp
  (implies (and (expev-meta-extract-global-facts)
                (pseudo-term-listp clause)
                (alistp a)
                (expev
                 (conjoin-clauses
                  (acl2::clauses-result
                   (expand-cp clause hints state)))
                 a))
           (expev (disjoin clause) a))
  :rule-classes :clause-processor)
)
