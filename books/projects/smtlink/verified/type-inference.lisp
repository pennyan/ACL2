;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 16th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "hint-please")
(include-book "hint-interface")
(include-book "extractor")
(include-book "type-theorems")
(include-book "basics")

(set-state-ok t)
;; Type inference takes the clause from the add-hyp-cp clause-processor and
;; apply type inference to the clause.
;; It produces a new clause that replace the clause with functions that are
;; typed.
;; This type inference is verified to be sound.

;; -----------------------------------------------------------------
;;       Define evaluators

(acl2::defevaluator-fast ev-infer ev-infer-lst
                         ((if a b c) (equal a b) (not a)
                          (cons a b) (binary-+ a b)
                          (typespec-check ts x)
                          (iff a b)
                          (implies a b)
                          (hint-please hint)
                          (return-last x y z)
                          (binary-+ x y))
                         :namedp t)

(acl2::def-ev-theoremp ev-infer)
(acl2::def-meta-extract ev-infer ev-infer-lst)
(acl2::def-unify ev-infer ev-infer-alist)

;; -----------------------------------------------------------------
;;                  some helper functions
(define type-list-to-alist ((type-lst pseudo-term-listp)
                            (fixinfo smt-fixtype-info-p))
  :returns (type-alist pseudo-term-alistp
                       :hints (("Goal" :in-theory (enable type-decl-p))))
  (b* ((type-lst (pseudo-term-list-fix type-lst))
       ((unless (consp type-lst)) nil)
       ((cons first rest) type-lst)
       ((unless (type-decl-p first fixinfo))
        (er hard? 'type-inference=>type-list-to-alist
            "Need a type-decl-p: ~q0" first))
       ((list & term) first))
    (acons term first
           (type-list-to-alist rest fixinfo))))

(define type-alist-to-type-list ((type-alst pseudo-term-alistp))
  :measure (len (pseudo-term-alist-fix type-alst))
  :returns (type-lst pseudo-term-listp)
  (b* ((type-alst (pseudo-term-alist-fix type-alst))
       ((unless (consp type-alst)) nil)
       ((cons first rest) type-alst))
    (cons (cdr first)
          (type-alist-to-type-list rest))))

(skip-proofs
 (defthm correctness-of-smt-extract-0
   (implies (and (ev-infer-meta-extract-global-facts)
                 (pseudo-term-listp cl)
                 (alistp a)
                 (not
                  (ev-infer
                   (conjoin
                    (mv-nth 0 (smt-extract (disjoin cl) fixinfo)))
                   a)))
            (ev-infer (disjoin cl) a))))

(skip-proofs
 (defthm correctness-of-smt-extract-1
   (implies (and (ev-infer-meta-extract-global-facts)
                 (pseudo-term-listp cl)
                 (alistp a)
                 (ev-infer
                  (mv-nth 1 (smt-extract (disjoin cl) fixinfo))
                  a))
            (ev-infer (disjoin cl) a))))

(skip-proofs
 (defthm correctness-of-type-list-to-alist
   (implies (and (ev-infer-meta-extract-global-facts)
                 (pseudo-term-listp type-lst)
                 (alistp a))
            (equal (ev-infer-lst
                    (type-alist-to-type-list
                     (type-list-to-alist type-lst fixinfo))
                    a)
                   (ev-infer-lst type-lst a)))))

(skip-proofs
 (defthm correctness-of-smt-extract
   (implies (and (ev-infer-meta-extract-global-facts)
                 (pseudo-term-listp cl)
                 (alistp a)
                 (not
                  (ev-infer
                   (conjoin
                    (type-alist-to-type-list
                     (type-list-to-alist
                      (mv-nth 0 (smt-extract (disjoin cl) fixinfo))
                      fixinfo)))
                   a)))
            (ev-infer (disjoin cl) a))))

;; -----------------------------------------------------------------

;; TODO
(define list-type? ((x symbolp))
  :returns (ok booleanp)
  :ignore-ok t
  t)

(define alist-type? ((x symbolp))
  :returns (ok booleanp)
  :ignore-ok t
  t)

(define option-type? ((x symbolp))
  :returns (ok booleanp)
  :ignore-ok t
  t)


;; ...update to recognize null to be a subtype of boolean alist list option
(define subtype-of ((type1 symbolp) (type2 symbolp))
  :returns (yes booleanp)
  (b* ((type1 (symbol-fix type1))
       (type2 (symbol-fix type2)))
    (cond ((equal type2 t) t)
          ((or (null type1) (null type2)) nil)
          ((equal type1 type2) t)
          ((and (equal type1 'null) (equal type2 'booleanp)) t)
          ((and (equal type1 'null) (list-type? type2)) t)
          ((and (equal type1 'null) (alist-type? type2)) t)
          ((and (equal type1 'null) (option-type? type2)) t)
          ((and (equal type1 'integerp) (equal type2 'rationalp)) t)
          ((and (equal type1 'integerp) (equal type2 'realp)) t)
          ((and (equal type1 'rationalp) (equal type2 'realp)) t)
          ((and (equal type1 'integerp) (equal type2 'real/rationalp)) t)
          ((and (equal type1 'rationalp) (equal type2 'real/rationalp)) t)
          ((and (equal type1 'real/rationalp) (equal type2 'realp) ) t)
          (t nil))))

(define lu-bound ((type1 symbolp) (type2 symbolp))
  :returns (bound symbolp)
  (b* ((type1 (symbol-fix type1))
       (type2 (symbol-fix type2))
       ((if (subtype-of type1 type2))
        type2)
       ((if (subtype-of type2 type1))
        type1))
    nil))

(define lu-bound-list ((type-lst symbol-listp))
  :returns (bound symbolp)
  :measure (len type-lst)
  (b* ((type-lst (symbol-list-fix type-lst))
       ((unless (consp type-lst))
        (er hard? 'type-inference
            "I don't know what to return for the least upper bound of no
             types.~%"))
       ((unless (consp (cdr type-lst)))
        (car type-lst)))
    (lu-bound (car type-lst) (lu-bound-list (cdr type-lst)))))

(define update-with-expected ((term pseudo-termp)
                              (type-alst pseudo-term-alistp)
                              (infered symbolp)
                              (expected symbolp))
  :returns (new-alst pseudo-term-alistp)
  (b* ((term (pseudo-term-fix term))
       (type-alst (pseudo-term-alist-fix type-alst))
       (infered (symbol-fix infered))
       (expected (symbol-fix expected))
       ((unless (subtype-of infered expected))
        (er hard? 'type-inference=>update-with-expected
            "Expected type ~p0 but ~p1 is of type ~p2~%"
            expected term infered)))
    (acons term `(,infered ,term) type-alst)))

;; What constants are recognized
;; 1 2 3 ... integerp
;; 1/1 1/2 ... rationalp
;; 'test ... symbolp
;; nil t ... booleanp
;; These ones are not supported yet
;; '(1 2 3) ... integer-listp
;; '(1/1 1/2 ...) ... rational-listp
;; '(a b c) ... symbol-listp
;; '(t nil nil ...) ... boolean-listp
(define infer-constant ((term pseudo-termp)
                        (type-alst pseudo-term-alistp)
                        (expected-type symbolp))
  :guard (and (not (acl2::variablep term))
              (acl2::fquotep term))
  :returns (new-type-alst pseudo-term-alistp)
  (b* ((term (pseudo-term-fix term))
       (type-alst (pseudo-term-alist-fix type-alst))
       ((if (acl2::variablep term)) nil)
       ((unless (acl2::fquotep term)) nil)
       (const (cadr term)))
    (cond ((integerp const)
           (update-with-expected term type-alst 'integerp expected-type))
          ((rationalp const)
           (update-with-expected term type-alst 'rationalp expected-type))
          ((null const)
           (update-with-expected term type-alst 'null expected-type))
          ((booleanp const)
           (update-with-expected term type-alst 'booleanp expected-type))
          ((symbolp const)
           (update-with-expected term type-alst 'symbolp expected-type))
          (t
           (er hard? 'type-inference=>infer-constant "Type inference for constant
term ~p0 is not supported yet. ~%" term)))))

(define typing-rules ()
  `((equal . equal-theorem)
    (< . <-theorem)

    ((binary-+ integerp integerp) . binary-+-of-integerp)
    ((binary-+ rationalp integerp) . binary-+-of-rational-integerp)
    ((binary-+ integerp rationalp) . binary-+-of-integer-rationalp)
    ((binary-+ rationalp rationalp) . binary-+-of-rationalp)

    ((unary-- integerp) . unary---of-integerp)
    ((unary-- rationalp) . unary---of-rationalp)

    ((binary-* integerp integerp) . binary-*-of-integerp)
    ((binary-* rationalp integerp) . binary-*-of-rational-integerp)
    ((binary-* integerp rationalp) . binary-*-of-integer-rationalp)
    ((binary-* rationalp rationalp) . binary-*-of-rationalp)

    ((unary-/ integerp) . unary-/-of-integerp)
    ((unary-/ rationalp) . unary-/-of-rationalp)

    (not . not-theorem)
    (if . if-theorem)
    (implies . implies-theorem)
    ))

(define expected-types ()
  `((equal . (t t))
    (< . (t t))
    (binary-+ . (t t))
    (unary-- . (t))
    (binary-* . (t t))
    (unary-/ . (t))
    (not . (booleanp))
    (if . (booleanp t t))
    (implies . (booleanp booleanp))
    (car . (t))
    (cdr . (t))
    )
  )

(define basic-expected ((fn symbolp))
  :returns (expected symbol-listp)
  (cdr (assoc-equal fn (expected-types))))

(define basic-fns ()
  '(equal < binary-+ unary-- binary-* unary-/ not if implies car cdr))

(define numerical-types ()
  '(integerp rationalp realp real/rationalp))

(define basic-fn-p ((fn symbolp))
  (member-equal fn (basic-fns)))

(define numerical-type-p ((tp symbolp))
  :returns (ok booleanp)
  (not (equal (member-equal tp (numerical-types)) nil)))

(define numerical-type-listp ((fn-lst symbol-listp))
  :returns (ok booleanp)
  :measure (len (symbol-list-fix fn-lst))
  (b* ((fn-lst (symbol-list-fix fn-lst))
       ((unless (consp fn-lst)) t)
       ((cons first rest) fn-lst))
    (and (numerical-type-p first)
         (numerical-type-listp rest))))

(defoption maybe-nat natp
  :pred maybe-natp)

(define get-type ((term pseudo-termp)
                  (type-alst pseudo-term-alistp))
  :returns (type symbolp)
  (b* ((term (pseudo-term-fix term))
       (type-alst (pseudo-term-alist-fix type-alst))
       (the-item (assoc-equal term type-alst))
       ((unless the-item) nil)
       (type-term (cdr the-item))
       ((unless (and (consp type-term) (symbolp (car type-term))))
        (er hard? 'type-inference=>get-type
            "The typed term is not a type predicate: ~q0" type-term)))
    (car type-term)))

(define get-type-list ((term-lst pseudo-term-listp)
                       (type-alst pseudo-term-alistp))
  :returns (type-list symbol-listp)
  :measure (len (pseudo-term-list-fix term-lst))
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       ((unless (consp term-lst)) nil)
       ((cons first rest) term-lst)
       (first-type (get-type first type-alst))
       (rest-types (get-type-list rest type-alst)))
    (cons first-type rest-types))
  ///
  (more-returns
   (type-list (true-listp type-list)
              :name true-listp-of-type-list-of-get-type-list)))

(define add-suffix ((sym symbolp)
                    (suffix stringp))
  :returns (new-sym symbolp)
  (b* ((sym (symbol-fix sym))
       (sym-str (symbol-name sym))
       (new-str (concatenate 'string sym-str suffix)))
    (intern-in-package-of-symbol new-str sym)))

(define remove-suffix ((sym symbolp) (suffix stringp))
  :returns (new-sym symbolp)
  (b* ((sym (symbol-fix sym))
       (sym-str (symbol-name sym))
       ((unless (>= (length sym-str)
                    7))
        sym)
       (pos (str::search suffix sym-str))
       ((unless (and (rationalp pos)
                     (>= pos 0)
                     (<= pos (length sym-str))))
        sym))
    (intern-in-package-of-symbol
     (str::subseq sym-str 0 pos)
     sym)))

(verify-termination std::defguts-p)
(verify-termination std::defguts)
(verify-guards std::defguts)
(verify-termination std::defguts->raw-formals$inline)
(verify-guards std::defguts->raw-formals$inline)
(verify-termination std::defguts->returnspecs$inline)
(verify-guards std::defguts->returnspecs$inline)
(verify-termination std::returnspec-p)
(verify-termination std::returnspec->return-type$inline)
(verify-guards std::returnspec->return-type$inline)

(define get-define-guts-alist ((world plist-worldp))
  :returns (guts alistp)
  (b* ((tb (table-alist 'define world))
       ((unless (alistp tb))
        (prog2$ (er hard? 'type-inference=>get-define-guts-alist
                    "(table-alist 'define world) returned something that's not
                    an alist.~%")
                (std::make-defguts)))
       (guts-alist (cdr (assoc 'std::guts-alist tb)))
       ((unless (alistp guts-alist))
        (prog2$ (er hard? 'type-inference=>get-define-guts-alist
                    "~p0 is not a alistp.~%")
                (std::make-defguts))))
    guts-alist))

(define get-guards ((fn symbolp)
                    state)
  :returns (guards symbol-listp)
  :guard-hints
  (("Goal"
    :in-theory (disable consp-of-pseudo-lambdap
                        symbol-listp
                        acl2::pseudo-lambdap-when-pseudo-termp
                        assoc-equal
                        default-car
                        std::defguts-p
                        pseudo-termp)))
  (b* ((fn (remove-suffix fn "$INLINE"))
       (gut (assoc-equal fn (get-define-guts-alist (w state))))
       ((unless (and (consp gut) (std::defguts-p (cdr gut))))
        (er hard? 'type-inference=>get-guards
            "Can't find function ~p0 in the std::defguts table.~%" fn))
       ((unless (acl2::all->=-len (std::defguts->raw-formals (cdr gut)) 2))
        (er hard? 'type-inference=>get-guards
            "....~%" fn))
       (guards (strip-cadrs (std::defguts->raw-formals (cdr gut))))
       ((unless (symbol-listp guards))
        (er hard? 'type-inference=>get-guards
            "Guards of ~p0 is not a list of symbols ~p1~%" fn guards)))
    guards))

(define get-return ((fn symbolp)
                    (fixinfo smt-fixtype-info-p)
                    state)
  :returns (ret symbolp
                :hints
                (("Goal"
                  :in-theory (disable consp-of-pseudo-lambdap
                                      symbol-listp
                                      acl2::pseudo-lambdap-when-pseudo-termp
                                      fgetprop
                                      pseudo-termp))))
  :guard-hints
  (("Goal"
    :in-theory (disable consp-of-pseudo-lambdap
                        symbol-listp
                        acl2::pseudo-lambdap-when-pseudo-termp
                        assoc-equal
                        default-car
                        std::defguts-p
                        pseudo-termp)))
  (b* ((fn (remove-suffix fn "$INLINE"))
       (gut (assoc-equal fn (get-define-guts-alist (w state))))
       ((unless (and (consp gut) (std::defguts-p (cdr gut))))
        (er hard? 'type-inference=>get-return
            "Can't find function ~p0 in the std::defguts table.~%" fn))
       (returnspecs (std::defguts->returnspecs (cdr gut)))
       ((unless (and (consp returnspecs) (std::returnspec-p (car returnspecs))
                     (null (cdr returnspecs))))
        (er hard? 'type-inference=>get-return
            "Currently only functions that returns one argument is supported
                    ~p0~%" fn))
       (returnspec (std::returnspec->return-type (car returnspecs)))
       ((unless (and (pseudo-termp returnspec) (type-decl-p returnspec fixinfo)))
        (er hard? 'type-inference=>get-return
            "Return spec for ~p0 is not a type-decl-p ~p1.~%" fn returnspec)))
    (car returnspec)))

(define get-expected-types ((fn symbolp)
                            (state))
  :returns (expected-types symbol-listp)
  (b* ((fn (symbol-fix fn))
       ((if (basic-fn-p fn)) (basic-expected fn)))
    (get-guards fn state)))

(define calculate-bound ((bound pseudo-termp))
  `((bound (lu-bound-list ,bound))
    ((unless bound)
     (er hard? 'type-inference=>make-judgement
         "Type inference failed. Can't calculate ~
          the least upper bound of the types of arguments to: ~
          ~%~p0 : ~p1~%"
         `(,fn ,@actuals) ,bound))))

(define check-numerical ()
  `(((unless (numerical-type-listp types))
     (er hard? 'type-inference=>make-judgement
         "Inputs to ~p0 are required to be numerical
         types, but ~p1 are of typespec-check ~p2~%"
         `(,fn ,@actuals) actuals types))))

(define check-nargs ((nargs natp))
  `(((unless (equal (len actuals) ,nargs))
     (er hard? 'type-inference=>make-judgement
         "Number of arguments is violated. ~p0 takes ~p1 arguments but is fed
                     with ~p2.~%"
         `(,fn ,@actuals) ,nargs (len actuals)))))

(define judgement-fn ((nargs maybe-natp)
                      (get-type booleanp)
                      (bound pseudo-termp)
                      (numerical booleanp))
  (b* ((nargs (maybe-nat-fix nargs))
       (nargs-code (if nargs (check-nargs nargs) nil))
       (type-code (if get-type
                      '((types (get-type-list actuals type-alst)))
                    nil))
       (numerical-code (if numerical (check-numerical) nil))
       (bound-code (if bound (calculate-bound bound) nil)))
    `(,@nargs-code
      ,@type-code
      ,@numerical-code
      ,@bound-code)))

(defmacro judgement (&key (nargs 'nil) (get-type 't)
                          (bound 'nil) (numerical 'nil) (returned 'nil))
  `(b* ,(judgement-fn nargs get-type bound numerical)
     ,returned))

;; TODO: I will change this function to extract the name of the elt-type from a
;; theorem instead of assuming the name convention later.
(define elt-type-of-list-type ((x symbolp))
  :returns (fixer symbolp)
  (b* ((x (symbol-fix x))
       (removed-x (remove-suffix x "-LISTP"))
       (added-x (add-suffix removed-x "P")))
    added-x))

(define make-judgement ((fn symbolp)
                        (actuals pseudo-term-listp)
                        (type-alst pseudo-term-alistp)
                        (fixinfo smt-fixtype-info-p)
                        state)
  :guard (not (equal fn 'quote))
  :returns (return-type symbolp)
  :guard-hints (("Goal"
                 :in-theory (disable true-listp-of-type-list-of-get-type-list)
                 :use ((:instance true-listp-of-type-list-of-get-type-list
                                  (term-lst actuals)
                                  (type-alst type-alst)))))
  (b* ((fn (symbol-fix fn))
       (type-alst (pseudo-term-alist-fix type-alst))
       ((unless (mbt (not (equal fn 'quote)))) nil))
    (case-match fn
      ('equal (judgement :nargs 2 :bound types :numerical nil :returned 'booleanp))
      ('< (judgement :nargs 2 :bound types :numerical t :returned 'booleanp))
      ('binary-+ (judgement :nargs 2 :bound types :numerical t :returned bound))
      ('unary-- (judgement :nargs 1 :bound nil :numerical t :returned (car types)))
      ('binary-* (judgement :nargs 2 :bound types :numerical t :returned bound))
      ('unary-/ (judgement :nargs 1 :bound types :numerical t :returned bound))
      ('not (judgement :nargs 1 :get-type nil
                       :bound nil :numerical nil :returned 'booleanp))
      ('if (judgement :nargs 3 :bound (cdr types) :numerical nil
                      :returned 'booleanp))
      ('implies (judgement :nargs 2 :get-type nil :bound nil :numerical nil
                           :returned 'booleanp))
      ('car (judgement :nargs 1 :bound nil :numerical nil
                       :returned (elt-type-of-list-type (car types))))
      ('cdr (judgement :nargs 1 :bound nil :numerical nil
                       :returned (car types)))
      (& (get-return fn fixinfo state))
      ;; ('cons )
      ;; ('acons )
      ;; ('assoc-equal )
      )))

(define infer-fncall-cons ((fn symbolp)
                           (actuals pseudo-term-listp)
                           (type-alst pseudo-term-alistp)
                           (expected-type symbolp)
                           (fixinfo smt-fixtype-info-p)
                           state)
  :irrelevant-formals-ok t
  :ignore-ok t
  :returns (new-alst pseudo-term-alistp)
  (pseudo-term-alist-fix type-alst))

(defines infer-type
  :well-founded-relation l<
  :verify-guards nil

  (define infer-fncall ((fn symbolp)
                        (actuals pseudo-term-listp)
                        (type-alst pseudo-term-alistp)
                        (expected-type symbolp)
                        (fixinfo smt-fixtype-info-p)
                        state)
    :guard (not (equal fn 'quote))
    :returns (new-alst pseudo-term-alistp)
    :measure (list (acl2-count (pseudo-term-list-fix actuals)) 1)
    (b* ((fn (symbol-fix fn))
         (actuals (pseudo-term-list-fix actuals))
         (type-alst (pseudo-term-alist-fix type-alst))
         ((unless (mbt (not (equal fn 'quote)))) type-alst)
         ((if (equal fn 'cons))
          (infer-fncall-cons fn actuals type-alst expected-type fixinfo state))
         (expected-types (get-expected-types fn state))
         (actuals-type-alst
          (infer-type-list actuals type-alst expected-types fixinfo state))
         (return-type (make-judgement fn actuals actuals-type-alst fixinfo state))
         ((unless (subtype-of return-type expected-type))
          (er hard? 'type-inference=>infer-fncall
              "Expected type ~p0 but ~p1 is of type ~p2~%"
              expected-type `(,fn ,@actuals) return-type)))
      (acons `(,fn ,@actuals)
             `(,return-type (,fn ,@actuals))
             actuals-type-alst)))

  (define infer-type ((term pseudo-termp)
                      (type-alst pseudo-term-alistp)
                      (expected-type symbolp)
                      (fixinfo smt-fixtype-info-p)
                      state)
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :returns (new-type-alst pseudo-term-alistp)
    (b* ((term (pseudo-term-fix term))
         (type-alst (pseudo-term-alist-fix type-alst))
         (- (cw "term: ~q0" term))
         (- (cw "type-alst: ~q0" type-alst))
         (item (assoc-equal term type-alst))
         ((if item) type-alst)
         ((if (acl2::variablep term))
          (er hard? 'type-inferece=>infer-type "Variable ~p0 isn't typed in the
                    environment.~%" term))
         ((if (acl2::fquotep term))
          (infer-constant term type-alst expected-type))
         ((cons fn actuals) term)
         ((if (pseudo-lambdap fn)) type-alst))
      (infer-fncall fn actuals type-alst expected-type fixinfo state)))

  (define infer-type-list ((term-lst pseudo-term-listp)
                           (type-alst pseudo-term-alistp)
                           (expected-type-lst symbol-listp)
                           (fixinfo smt-fixtype-info-p)
                           state)
    :measure (list (acl2-count (pseudo-term-list-fix term-lst)) 0)
    :returns (new-type-alst pseudo-term-alistp)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (type-alst (pseudo-term-alist-fix type-alst))
         ((unless (consp term-lst)) type-alst)
         ((cons first rest) term-lst)
         ((cons first-expected rest-expected) expected-type-lst)
         (first-alst
          (infer-type first type-alst first-expected fixinfo state))
         (rest-alst
          (infer-type-list rest first-alst rest-expected fixinfo state)))
      rest-alst))

  )

(verify-guards infer-type)

(local
 (in-theory (enable pseudo-term-listp)))

(define infer-type-fn ((cl pseudo-term-listp)
                       (smtlink-hint t)
                       state)
  :returns (subgoal-lst pseudo-term-list-listp)
  :irrelevant-formals-ok t
  :ignore-ok t
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint))
        (list cl))
       ((smtlink-hint h) smtlink-hint)
       ((mv type-hyp-lst untyped-theorem)
        (smt-extract (disjoin cl) h.types-info))
       (type-alist (type-list-to-alist type-hyp-lst h.types-info))
       (new-hyp (infer-type untyped-theorem type-alist t h.types-info state))
       (- (cw "types: ~q0" new-hyp))
       ;; (new-cl `((implies ,(conjoin (type-alist-to-type-list new-hyp))
       ;; ,new-thm)))
       (new-cl `((implies ,(conjoin (type-alist-to-type-list type-alist))
                          ,untyped-theorem)))
       (next-cp (cdr (assoc-equal 'infer-type *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',h state)))
       (hinted-goal `((hint-please ',the-hint) ,@new-cl)))
    (list hinted-goal)))

(define infer-type-cp ((cl pseudo-term-listp)
                       (hints t)
                       state)
  (b* ((infered-clause (infer-type-fn cl hints state)))
    (value infered-clause)))

(local (in-theory (enable infer-type-cp infer-type-fn infer-type)))

(skip-proofs
 (defthm correctness-of-infer-type-cp
   (implies (and (ev-infer-meta-extract-global-facts)
                 (pseudo-term-listp cl)
                 (alistp a)
                 (ev-infer
                  (conjoin-clauses
                   (acl2::clauses-result
                    (infer-type-cp cl hint state)))
                  a))
            (ev-infer (disjoin cl) a))
   :rule-classes :clause-processor)
 )
