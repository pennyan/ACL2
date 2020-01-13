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

(include-book "basics")
(include-book "hint-please")
(include-book "term-substitution")

;; ---------------------------------------------------

;; Datatypes and functions that operates them

;; This is a version where a type can have multiple supertypes
;; (defalist type-to-supertypes-alist
;;   :key-type symbolp
;;   :val-type symbol-listp
;;   :true-listp t)

;; (defthm assoc-equal-of-type-to-supertypes-alist
;;   (implies (and (type-to-supertypes-alist-p x)
;;                 (assoc-equal y x))
;;            (consp (assoc-equal y x))))

(defalist type-to-supertype-alist
  :key-type symbolp
  :val-type symbolp
  :true-listp t)

(defthm assoc-equal-of-type-to-supertype-alist
  (implies (and (type-to-supertype-alist-p x)
                (assoc-equal y x))
           (consp (assoc-equal y x))))

(defprod type-tuple
  ((type symbolp)
   (super-type symbolp)))

(defalist type-tuple-to-thm-alist
  :key-type type-tuple-p
  :val-type symbolp
  :true-listp t)

(defprod return-spec
  ((return-type symbolp)
   (returns-thm symbolp)))

(deflist return-spec-list
  :elt-type return-spec-p
  :true-listp t)

(fty::deftypes function-description
  (deftagsum arg-decl
    (:next ((next arg-check-p)))
    (:done ((r return-spec-p))))
  (defalist arg-check
    :key-type symbolp
    :val-type arg-decl-p))

(defalist function-description-alist
  :key-type symbolp
  :val-type arg-decl-p
  :true-listp t)

(defthm arg-decl-p-of-assoc-equal-from-function-description-alist-p
  (implies (and (function-description-alist-p y)
                (assoc-equal x y))
           (and (consp (assoc-equal x y))
                (arg-decl-p (cdr (assoc-equal x y))))))

(defprod basic-type-description
  ((recognizer symbolp)
   (fixer symbolp)))

(defalist basic-type-description-alist
  :key-type symbolp
  :val-type basic-type-description-p
  :true-listp t)

(defprod cons-type-description
  ((recognizer symbolp)
   (fixer symbolp)
   (car-type symbolp)
   (cdr-type symbolp)
   (cdr-thm symbolp)))

(defalist cons-type-description-alist
  :key-type symbolp
  :val-type cons-type-description-p
  :true-listp t)

(encapsulate ()
(local (in-theory (disable (:rewrite default-cdr))))
(defprod list-type-description
  ((recognizer symbolp)
   (fixer symbolp)
   (elt-type symbolp)
   (cons-thm symbolp)
   (car-thm symbolp)
   (cdr-thm symbolp)
   (nil-thm symbolp)))

(defalist list-type-description-alist
  :key-type symbolp
  :val-type list-type-description-p
  :true-listp t)

(defprod alist-type-description
  ((recognizer symbolp)
   (fixer symbolp)
   (key-type symbolp)
   (val-type symbolp)
   (acons-thm symbolp)
   (assoc-equal-thm symbolp)
   (nil-thm symbolp)))

(defalist alist-type-description-alist
  :key-type symbolp
  :val-type alist-type-description-p
  :true-listp t)
)

(encapsulate ()
  (local (in-theory (disable (:rewrite default-cdr)
                             (:rewrite consp-of-pseudo-lambdap)
                             (:rewrite
                              acl2::pseudo-lambdap-of-car-when-pseudo-termp)
                             (:definition pseudo-termp)
                             (:rewrite
                              acl2::true-listp-of-car-when-true-list-listp)
                             (:definition true-list-listp)
                             (:rewrite
                              acl2::true-list-listp-of-cdr-when-true-list-listp)
                             (:definition true-listp)
                             (:rewrite pseudo-term-listp-of-symbol-listp)
                             (:definition symbol-listp))))
(defprod prod-type-description
  ((recognizer symbolp)
   (fixer symbolp)
   (field-types symbol-listp)
   (constructor-thm symbolp)
   (destructor-thms symbol-listp)))

(defalist prod-type-description-alist
  :key-type symbolp
  :val-type prod-type-description-p
  :true-listp t)

(defprod option-type-description
  ((recognizer symbolp)
   (fixer symbolp)
   (some-type symbolp)
   (some-constructor-thm symbolp)
   (none-constructor-thm symbolp)
   (some-destructor-thm symbolp)
   (non-nil-thm symbolp)
   (nil-thm symbolp)))

(defalist option-type-description-alist
  :key-type symbolp
  :val-type option-type-description-p
  :true-listp t)

(defprod sum-type-description
  ((prod-list prod-type-description-alist-p)))

(defalist sum-type-description-alist
  :key-type symbolp
  :val-type sum-type-description-p
  :true-listp t)

(defprod abstract-type-description
  ((recognizer symbolp)
   (fixer symbolp)))

(defalist abstract-type-description-alist
  :key-type symbolp
  :val-type abstract-type-description-p
  :true-listp t)

(defprod type-options
  ((supertype type-to-supertype-alist-p)
   (supertype-thm type-tuple-to-thm-alist-p)
   (functions function-description-alist-p)
   (consp cons-type-description-alist-p)
   (basic basic-type-description-alist-p)
   (list list-type-description-alist-p)
   (alist alist-type-description-alist-p)
   (prod prod-type-description-alist-p)
   (option option-type-description-alist-p)
   (sum sum-type-description-alist-p)
   (abstract abstract-type-description-alist-p)))
)

(define is-maybe-type? ((type symbolp)
                        (option option-type-description-alist-p))
  :returns (ok booleanp)
  (not (null (assoc-equal type (option-type-description-alist-fix option)))))

(define get-nonnil-thm ((type symbolp)
                        (option option-type-description-alist-p))
  :returns (thm symbolp)
  (b* ((option (option-type-description-alist-fix option))
       (conspair (assoc-equal type option))
       ((unless conspair)
        (er hard? 'type-inference=>get-nonnil-thm
            "Can't find type ~p0 in the option-type alist.~%" type))
       (type-description (cdr conspair)))
    (option-type-description->non-nil-thm type-description)))

(define is-type? ((type symbolp)
                  (supertype-alst type-to-supertype-alist-p))
  :returns (ok booleanp)
  (not (null (assoc-equal type (type-to-supertype-alist-fix supertype-alst)))))

;; ------------------------

(define only-one-var-acc ((term-lst pseudo-term-listp)
                          (count natp))
  :returns (ok booleanp)
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       (count (nfix count))
       ((unless (consp term-lst)) (equal count 1))
       ((cons first rest) term-lst)
       ((if (acl2::variablep first))
        (only-one-var-acc rest (1+ count)))
       ((if (acl2::fquotep first))
        (only-one-var-acc rest count)))
    nil))

(define only-one-var ((term-lst pseudo-term-listp))
  :returns (ok booleanp)
  (only-one-var-acc (pseudo-term-list-fix term-lst) 0))

(define type-predicate-p ((judge t)
                          (supertype-alst type-to-supertype-alist-p))
  :returns (ok booleanp)
  (and (pseudo-termp judge)
       (equal (len judge) 2)
       (symbolp (car judge))
       (not (equal (car judge) 'quote))
       (is-type? (car judge) supertype-alst))
  ///
  (more-returns
   (ok (implies ok
                (and (symbolp (car judge))
                     (consp judge)
                     (pseudo-termp (cadr judge))))
       :name more-returns-of-type-predicate-p)
   (ok (implies ok
                (true-listp judge))
       :name true-listp-of-type-predicate)))

(define single-var-fncall-p ((judge t))
  :returns (ok booleanp)
  (and (pseudo-termp judge)
       (consp judge)
       (symbolp (car judge))
       (not (equal (car judge) 'quote))
       (only-one-var (cdr judge)))
  ///
  (more-returns
   (ok (implies ok
                (true-listp judge))
       :name true-listp-of-single-var-fncall)))

(define judgement-p ((judge t)
                     (supertype-alst type-to-supertype-alist-p))
  :returns (ok booleanp)
  (or (type-predicate-p judge supertype-alst)
      (single-var-fncall-p judge))
  ///
  (more-returns
   (ok (implies ok
                (true-listp judge))
       :name true-listp-of-judgement)))

(define is-conjunct? ((term pseudo-termp))
  :returns (ok booleanp)
  (b* ((term (pseudo-term-fix term)))
    (implies (not (equal term ''t))
             (and (consp term)
                  (equal (car term) 'if)
                  (equal (len term) 4)
                  (equal (cadddr term) ''nil))))
  ///
  (more-returns
   (ok (implies (and ok (pseudo-termp term) (not (equal term ''t)))
                (and (consp term)
                     (equal (len term) 4)
                     (pseudo-termp (cadr term))
                     (pseudo-termp (caddr term))))
       :name implies-of-is-conjunct?)
   (ok (implies (and ok (pseudo-termp term) (not (equal term ''t)))
                (< (acl2-count (caddr term))
                   (acl2-count term)))
       :name acl2-count-of-caddr-of-is-conjunct?
       :hints (("Goal"
                :in-theory (disable implies-of-is-conjunct?
                                    symbol-listp)))
       :rule-classes :linear)))

(local
 (defthm is-conjunct?-very-stupid
   (implies (and (pseudo-termp actuals-judgements)
                 (not (equal actuals-judgements ''t))
                 (is-conjunct? actuals-judgements))
            (and (consp (cdr actuals-judgements))
                 (consp (cddr actuals-judgements))))
   :hints (("Goal"
            :in-theory (enable is-conjunct?)))
   )
 )

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

(set-state-ok t)

(define eval-const-expr ((expr pseudo-termp) state)
  :returns (val acl2::any-p)
  (b* ((expr (pseudo-term-fix expr))
       ((mv err val) (acl2::magic-ev expr nil state t nil))
       ((if err)
        (er hard? 'type-inference=>eval-const-expr val)))
    val))

(define path-cond-implies-expr-not-nil ((path-cond pseudo-termp)
                                        (expr pseudo-termp)
                                        state)
  :returns (ok booleanp)
  :measure (acl2-count (pseudo-term-fix path-cond))
  (b* ((path-cond (pseudo-term-fix path-cond))
       (expr (pseudo-term-fix expr))
       ((unless (is-conjunct? path-cond))
        (er hard? 'type-inference=>path-cond-implies-expr-not-nil
            "Path condition is not a conjunction of conditions: ~q0" path-cond))
       ((if (equal path-cond ''t)) nil)
       ((list* & path-hd path-tl &) path-cond)
       (path-hd-nil/expr (term-substitution path-hd expr ''nil t))
       ((if (and (null (all-vars path-hd-nil/expr))
                 (null (eval-const-expr path-hd-nil/expr state)))) t))
    (path-cond-implies-expr-not-nil path-tl expr state)))

(define path-cond-conj-implies-expr-not-nil ((path-cond-conj pseudo-termp)
                                             (expr pseudo-termp)
                                             state)
  :returns (ok booleanp)
  :measure (acl2-count (pseudo-term-fix path-cond-conj))
  (b* ((path-cond-conj (pseudo-term-fix path-cond-conj))
       ((unless (is-conjunct? path-cond-conj))
        (er hard? 'type-inference=>path-cond-conj-implies-expr-not-nil
            "Path-cond conjunction is malformed: ~q0" path-cond-conj))
       ((if (equal path-cond-conj ''t)) nil)
       ((list & path-cond-hd path-cond-tl &) path-cond-conj)
       (yes? (path-cond-implies-expr-not-nil path-cond-hd expr state))
       ((if yes?) t))
    (path-cond-conj-implies-expr-not-nil path-cond-tl expr state)))

(define path-cond-conj-implies-expr-list ((path-cond-conj pseudo-termp)
                                          (expr-conj pseudo-termp)
                                          state)
  :returns (ok booleanp)
  :measure (acl2-count (pseudo-term-fix expr-conj))
  (b* ((path-cond-conj (pseudo-term-fix path-cond-conj))
       (expr-conj (pseudo-term-fix expr-conj))
       ((unless (is-conjunct? expr-conj))
        (path-cond-conj-implies-expr-not-nil path-cond-conj expr-conj state))
       ((if (equal expr-conj ''t)) nil)
       ((list & expr-hd expr-tl &) expr-conj)
       (yes? (path-cond-conj-implies-expr-not-nil path-cond-conj expr-hd state))
       ((if yes?) (path-cond-conj-implies-expr-list path-cond-conj expr-tl state)))
    nil))

(encapsulate ()
  (local
   (in-theory (disable (:definition symbol-listp)
                       (:rewrite
                        pseudo-term-listp-of-cdr-of-pseudo-termp)
                       (:rewrite
                        acl2::true-listp-of-car-when-true-list-listp)
                       (:definition true-list-listp))))

(define look-up-path-cond ((term pseudo-termp)
                           (path-cond pseudo-termp)
                           (supertype-alst type-to-supertype-alist-p))
  :returns (type-term
            pseudo-termp
            :hints (("Goal" :in-theory (disable symbol-listp))))
  :measure (acl2-count (pseudo-term-fix path-cond))
  :guard-hints (("Goal"
                 :in-theory (disable true-listp-of-judgement)
                 :use ((:instance true-listp-of-judgement
                                  (judge (cadr path-cond))))))
  (b* ((term (pseudo-term-fix term))
       (path-cond (pseudo-term-fix path-cond))
       ((unless (is-conjunct? path-cond))
        (er hard? 'type-inference=>look-up-path-cond
            "Path condition is not a conjunction of conditions: ~q0" path-cond))
       ((if (equal path-cond ''t)) ''t)
       ((list* & path-hd path-tl &) path-cond)
       ((unless (judgement-p path-hd supertype-alst))
        (look-up-path-cond term path-tl supertype-alst))
       ((if (member-equal term (cdr path-hd)))
        `(if ,path-hd
             ,(look-up-path-cond term path-tl supertype-alst)
           'nil)))
    (look-up-path-cond term path-tl supertype-alst)))
)

(define shadow-path-cond ((formals symbol-listp)
                          (path-cond pseudo-termp))
  :returns (shadowed-path-cond pseudo-termp)
  :measure (acl2-count (pseudo-term-fix path-cond))
  (b* ((formals (symbol-list-fix formals))
       (path-cond (pseudo-term-fix path-cond))
       ((unless (is-conjunct? path-cond))
        (er hard? 'type-inference=>shadow-path-cond
            "Path condition is not a conjunction of conditions: ~q0"
            path-cond))
       ((if (equal path-cond ''t)) ''t)
       ((list* & path-hd path-tl &) path-cond)
       (shadowed? (dumb-occur-vars-or formals path-hd))
       ((if shadowed?) (shadow-path-cond formals path-tl)))
    `(if ,path-hd
         ,(shadow-path-cond formals path-tl)
       'nil)))

;; return the topest judgement
(define type-judgement-top ((judgements pseudo-termp))
  :returns (judgement pseudo-termp)
  (b* ((judgements (pseudo-term-fix judgements))
       ((unless (is-conjunct? judgements))
        (er hard? 'type-inference=>type-judgement-top
            "The top of type judgement is not a conjunction of conditions: ~q0"
            judgements))
       ((if (equal judgements ''t))
        (er hard? 'type-inference=>type-judgement-top
            "The judgements is empty.~%")))
    (cadr judgements)))

(define type-judgement-top-list ((judgements-lst pseudo-termp))
  :returns (judgement-lst pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judgements-lst))
  (b* ((judgements-lst (pseudo-term-fix judgements-lst))
       ((unless (is-conjunct? judgements-lst))
        (er hard? 'type-inference=>type-judgement-top-list
            "The top of type judgement is not a conjunction of conditions: ~q0"
            judgements-lst))
       ((if (equal judgements-lst ''t)) ''t)
       ((list* & judgements-hd judgements-tl &) judgements-lst))
    `(if ,(type-judgement-top judgements-hd)
         ,(type-judgement-top-list judgements-tl)
       'nil)))

;;-----------------------
;;      subtyping

;; (defines supertype-transitive-closure
;;   :well-founded-relation l<
;;   :verify-guards nil

;;   (define supertype ((type symbolp)
;;                      (supertype-alst
;;                       type-to-supertypes-alist-p)
;;                      (closure symbol-listp)
;;                      (clock natp)) ;; clock is the length of the supertype-alst
;;     :measure (list (nfix clock) (acl2-count (symbol-fix type)))
;;     :returns (closure symbol-listp)
;;     (b* ((type (symbol-fix type))
;;          (supertype-alst (type-to-supertypes-alist-fix supertype-alst))
;;          (closure (symbol-list-fix closure))
;;          (clock (nfix clock))
;;          ((if (zp clock)) closure)
;;          (exist? (member-equal type closure))
;;          ((if exist?) closure)
;;          (new-closure (cons type closure))
;;          (item (assoc-equal type supertype-alst))
;;          ((unless item)
;;           (er hard? 'type-inference=>supertype
;;               "Type ~p0 doesn't exist in the supertype alist.~%" type))
;;          ((unless (cdr item)) new-closure)
;;          (supertype-lst (cdr item)))
;;       (supertype-list supertype-lst supertype-alst new-closure (1- clock))))

;;   (define supertype-list ((type-lst symbol-listp)
;;                           (supertype-alst
;;                            type-to-supertypes-alist-p)
;;                           (closure symbol-listp)
;;                           (clock natp))
;;     :measure (list (nfix clock) (acl2-count (symbol-list-fix type-lst)))
;;     :returns (closure symbol-listp)
;;     (b* ((type-lst (symbol-list-fix type-lst))
;;          (supertype-alst (type-to-supertypes-alist-fix supertype-alst))
;;          (closure (symbol-list-fix closure))
;;          (clock (nfix clock))
;;          ((unless (consp type-lst)) closure)
;;          ((cons type-hd type-tl) type-lst)
;;          (new-closure
;;           (supertype type-hd supertype-alst closure clock)))
;;       (supertype-list type-tl supertype-alst new-closure clock)))
;;   )
;;
;; (verify-guards supertype)

(defthm symbolp-of-cdr-of-assoc-equal-from-type-to-supertype-alist
  (implies (and (type-to-supertype-alist-p x)
                (assoc-equal y x))
           (symbolp (cdr (assoc-equal y x)))))

(define supertype-clocked ((type symbolp)
                           (supertype-alst
                            type-to-supertype-alist-p)
                           (clock natp))
  :returns (supertypes symbol-listp)
  :measure (nfix clock)
  (b* ((type (symbol-fix type))
       (supertype-alst (type-to-supertype-alist-fix supertype-alst))
       (clock (nfix clock))
       ((if (zp clock))
        (er hard? 'type-inference=>supertype
            "Run out of clocks.~%"))
       (conspair (assoc-equal type supertype-alst))
       ((unless (and conspair (cdr conspair))) nil))
    (cons (cdr conspair)
          (supertype-clocked (cdr conspair) supertype-alst (1- clock)))))

;; -----------------------------------------------------

(define look-up-type-tuple-to-thm-alist ((root-type symbolp)
                                         (super-type symbolp)
                                         (thms type-tuple-to-thm-alist-p)
                                         state)
  :returns (ok booleanp)
  :ignore-ok t
  (b* ((thms (type-tuple-to-thm-alist-fix thms))
       (tuple (make-type-tuple :type root-type
                               :super-type super-type))
       (conspair (assoc-equal tuple thms))
       ((unless conspair)
        (er hard? 'type-inference=>supertype-to-judgements
            "There doesn't exist a theorem supporting the supertype ~
             relationship between ~p0 and ~p1.~%"
            root-type super-type))
       (thm-name (cdr conspair))
       (supertype-thm
        (acl2::meta-extract-formula-w thm-name (w state)))
       ((unless (pseudo-termp supertype-thm))
        (er hard? 'type-inference=>supertype-to-judgements
            "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
            thm-name supertype-thm))
       (ok (case-match supertype-thm
             (('implies (!root-type var)
                        (!super-type var)) t)
             (& nil)))
       ((unless ok)
        (er hard? 'type-inference=>supertype-to-judgements
            "Supertype theorem is malformed: ~q0" supertype-thm)))
    t))

(encapsulate ()
  (local (in-theory (disable (:definition pseudo-termp)
                             (:rewrite lambda-of-pseudo-lambdap))))
  (local
   (defthm assoc-equal-of-type-tuple-to-thm-alist-p
     (implies (and (type-tuple-to-thm-alist-p x)
                   (assoc-equal y x))
              (and (consp (assoc-equal y x))
                   (symbolp (cdr (assoc-equal y x)))))))

(define supertype-to-judgements ((root-type symbolp)
                                 (supertypes symbol-listp)
                                 (term pseudo-termp)
                                 (thms type-tuple-to-thm-alist-p)
                                 (acc pseudo-termp)
                                 state)
  :returns (judgements pseudo-termp)
  :measure (len supertypes)
  (b* ((root-type (symbol-fix root-type))
       (supertypes (symbol-list-fix supertypes))
       (term (pseudo-term-fix term))
       (thms (type-tuple-to-thm-alist-fix thms))
       (acc (pseudo-term-fix acc))
       ((unless (consp supertypes)) acc)
       ((cons supertypes-hd supertypes-tl) supertypes)
       ((unless
            (look-up-type-tuple-to-thm-alist root-type supertypes-hd thms state))
        nil)
       (supertype-term `(,supertypes-hd ,term))
       ((if (path-cond-implies-expr-not-nil acc supertype-term state))
        (supertype-to-judgements root-type supertypes-tl term thms acc state)))
    (supertype-to-judgements root-type supertypes-tl term thms
                             `(if ,supertype-term ,acc 'nil) state)))
)

(define supertype-judgement-single ((type-judgement pseudo-termp)
                                    (supertype-alst
                                     type-to-supertype-alist-p)
                                    (thms type-tuple-to-thm-alist-p)
                                    (acc pseudo-termp)
                                    state)
  :returns (judgements pseudo-termp)
  (b* ((type-judgement (pseudo-term-fix type-judgement))
       (acc (pseudo-term-fix acc))
       ((unless (type-predicate-p type-judgement supertype-alst))
        (er hard? 'type-inference=>supertype-judgement-single
            "Type judgement ~p0 is malformed.~%" type-judgement))
       ((list root-type term) type-judgement)
       (supertype-alst (type-to-supertype-alist-fix supertype-alst))
       (clock (len supertype-alst))
       (supertypes
        (supertype-clocked root-type supertype-alst clock)))
    (supertype-to-judgements root-type supertypes term thms acc state)))

(define supertype-judgements-acc ((judge pseudo-termp)
                                  (supertype-alst
                                   type-to-supertype-alist-p)
                                  (thms type-tuple-to-thm-alist-p)
                                  (acc pseudo-termp)
                                  state)
  :returns (judgements pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judge))
  (b* ((judge (pseudo-term-fix judge))
       (acc (pseudo-term-fix acc))
       (- (cw "supertype-judgments-acc judge: ~q0" judge))
       ((unless (is-conjunct? judge))
        (er hard? 'type-inference=>supertype-judgements
            "~p0 is not a conjunction.~%" judge))
       ((if (equal judge ''t)) acc)
       ((list* & cond then &) judge)
       (first-acc
        (supertype-judgement-single cond supertype-alst thms acc state)))
    (supertype-judgements-acc then supertype-alst thms first-acc state)))

(define supertype-judgements ((judge pseudo-termp)
                              (supertype-alst
                               type-to-supertype-alist-p)
                              (thms type-tuple-to-thm-alist-p)
                              state)
  :returns (judgements pseudo-termp)
  (supertype-judgements-acc judge supertype-alst thms judge state))

#|
(defthm test (implies (integerp x) (rationalp x)))
(supertype-judgements '(if (integerp x) 't 'nil)
                      '((integerp . rationalp) (rationalp . nil))
                      '((((type . integerp) (super-type . rationalp)) . test))
                      state)
|#

(define supertype-of?-clocked ((type1 symbolp)
                               (type2 symbolp)
                               (supertype-alst type-to-supertype-alist-p)
                               (thms type-tuple-to-thm-alist-p)
                               (clock natp)
                               state)
  :returns (ok booleanp)
  :measure (nfix clock)
  (b* ((type1 (symbol-fix type1))
       (type2 (symbol-fix type2))
       (clock (nfix clock))
       ((if (zp clock))
        (er hard? 'type-inference=>supertype-of?-clocked
            "Run out of clock.~%"))
       ((if (equal type1 type2)) t)
       (conspair (assoc-equal type2 supertype-alst))
       ((unless conspair)
        (er hard? 'type-inference=>supertype-of?
            "Can't find ~p0 in type-to-supertype-alist.~%" type1))
       (supertype (cdr conspair))
       ((unless supertype) nil)
       ((unless (look-up-type-tuple-to-thm-alist type2 supertype thms state))
        nil))
    (supertype-of?-clocked type1 supertype supertype-alst thms (1- clock) state)))

(define supertype-of? ((type1 symbolp)
                       (type2 symbolp)
                       (supertype-alst type-to-supertype-alist-p)
                       (thms type-tuple-to-thm-alist-p)
                       state)
  :returns (ok booleanp)
  (supertype-of?-clocked type1 type2 supertype-alst thms
                         (len supertype-alst) state))

(define judgements-upper-bound ((judge1 pseudo-termp)
                                (judge2 pseudo-termp)
                                (supertype-alst type-to-supertype-alist-p)
                                (thms type-tuple-to-thm-alist-p)
                                state)
  :returns (upper-bound pseudo-termp)
  (b* ((judge1 (pseudo-term-fix judge1))
       (judge2 (pseudo-term-fix judge2))
       ((unless (and (type-predicate-p judge1 supertype-alst)
                     (type-predicate-p judge2 supertype-alst)))
        (er hard? 'type-inference=>judgements-upper-bound
            "~p0 or ~p1 are not type-predicate(s).~%" judge1 judge2))
       ((list* type1 term1) judge1)
       ((list* type2 term2) judge2)
       (- (cw "union type1 ~p0 and type2 ~p1~%" type1 type2))
       ((unless (equal term1 term2))
        (er hard? 'type-inference=>supertype-of?
            "Predicate ~p0 and ~p1 are for difference terms.~%"
            judge1 judge2))
       (judge1>=judge2? (supertype-of? type1 type2 supertype-alst thms state))
       ((if judge1>=judge2?) judge1)
       (judge2>=judge1? (supertype-of? type2 type1 supertype-alst thms state))
       ((if judge2>=judge1?) judge2))
    nil))

(define union-judgements-12lst ((judge pseudo-termp)
                                (judge-conj pseudo-termp)
                                (supertype-alst type-to-supertype-alist-p)
                                (thms type-tuple-to-thm-alist-p)
                                (acc pseudo-termp)
                                state)
  :measure (acl2-count (pseudo-term-fix judge-conj))
  :returns (union pseudo-termp)
  (b* ((judge (pseudo-term-fix judge))
       (judge-conj (pseudo-term-fix judge-conj))
       (acc (pseudo-term-fix acc))
       ((unless (is-conjunct? judge-conj))
        (er hard? 'type-inference=>union-judgements-12lst
            "~p0 is not a conjunction.~%" judge-conj))
       ((if (equal judge-conj ''t)) acc)
       ((list* & cond then &) judge-conj)
       (upper-bound
        (judgements-upper-bound judge cond supertype-alst thms state))
       ((unless upper-bound)
        (union-judgements-12lst judge then supertype-alst thms acc state))
       ((if (path-cond-implies-expr-not-nil acc upper-bound state))
        (union-judgements-12lst judge then supertype-alst thms acc state)))
    (union-judgements-12lst judge then supertype-alst thms
                            `(if ,upper-bound ,acc 'nil) state)))

(define union-judgements-lst2lst ((judge1 pseudo-termp)
                                  (judge2 pseudo-termp)
                                  (supertype-alst type-to-supertype-alist-p)
                                  (thms type-tuple-to-thm-alist-p)
                                  (acc pseudo-termp)
                                  state)
  :returns (union
            pseudo-termp
            :hints (("Goal" :in-theory (disable symbol-listp))))
  :measure (acl2-count (pseudo-term-fix judge1))
  (b* ((judge1 (pseudo-term-fix judge1))
       (judge2 (pseudo-term-fix judge2))
       (acc (pseudo-term-fix acc))
       (thms (type-tuple-to-thm-alist-fix thms))
       ((unless (is-conjunct? judge1))
        (er hard? 'type-inference=>union-judgements
            "~p0 is not a conjunction.~%" judge1))
       ((if (equal judge1 ''t)) acc)
       ((list* & cond then &) judge1)
       (hd-acc (union-judgements-12lst cond judge2 supertype-alst thms acc state)))
    (union-judgements-lst2lst then judge2 supertype-alst thms hd-acc state)))

;; Assumes judge1 and judge2 are type judgements over the same term
(define union-judgements ((judge1 pseudo-termp)
                          (judge2 pseudo-termp)
                          (supertype-alst type-to-supertype-alist-p)
                          (thms type-tuple-to-thm-alist-p)
                          state)
  :returns (union pseudo-termp)
  (union-judgements-lst2lst judge1 judge2 supertype-alst thms ''t state))

#|
(defthm test (implies (integerp x) (rationalp x)))
(union-judgements '(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
                  '(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
                  '((integerp . rationalp) (rationalp . nil))
                  '((((type . integerp) (super-type . rationalp)) . test))
                  state)

(union-judgements '(IF (MAYBE-RATIONAL-INTEGER-CONSP (IF (RATIONALP R1)
                                                         (ASSOC-EQUAL R1 AL)
                                                         'NIL))
                       'T
                       'NIL)
                  '(IF
                  (BOOLEANP (IF (RATIONALP R1)
                                (ASSOC-EQUAL R1 AL)
                                'NIL))
                  (IF
                   (SYMBOLP (IF (RATIONALP R1)
                                (ASSOC-EQUAL R1 AL)
                                'NIL))
                   (IF
                     (MAYBE-RATIONAL-INTEGER-CONSP (IF (RATIONALP R1)
                                                       (ASSOC-EQUAL R1 AL)
                                                       'NIL))
                     (IF (MAYBE-INTEGERP (IF (RATIONALP R1)
                                             (ASSOC-EQUAL R1 AL)
                                             'NIL))
                         (IF (RATIONAL-INTEGER-ALISTP (IF (RATIONALP R1)
                                                          (ASSOC-EQUAL R1 AL)
                                                          'NIL))
                             'T
                             'NIL)
                         'NIL)
                     'NIL)
                   'NIL)
                  'NIL)
                  '((maybe-rational-integer-consp . nil) (booleanp . nil)
                    (symbolp . nil) (maybe-integerp . nil)
                    (rational-integer-alistp . nil))
                  '()
                  state)
|#

;;-----------------------
(encapsulate ()
  (local (in-theory (disable (:definition assoc-equal)
                             (:definition symbol-listp)
                             (:rewrite consp-of-pseudo-lambdap)
                             (:definition pseudo-termp))))

(define construct-returns-judgement ((fn symbolp)
                                     (actuals pseudo-term-listp)
                                     (actuals-judgements pseudo-termp)
                                     (return-spec return-spec-p)
                                     state)
  :returns (judgement pseudo-termp)
  :guard (not (equal fn 'quote))
  :ignore-ok t
  (b* ((fn (symbol-fix fn))
       ((unless (mbt (not (equal fn 'quote)))) nil)
       (actuals (pseudo-term-list-fix actuals))
       (return-spec (return-spec-fix return-spec))
       (returns-name (return-spec->returns-thm return-spec))
       (return-type (return-spec->return-type return-spec))
       (returns-thm
        (acl2::meta-extract-formula-w returns-name (w state)))
       ((unless (pseudo-termp returns-thm))
        (er hard? 'type-inference=>construct-returns-judgement
            "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
            returns-name returns-thm))
       ((mv ok type)
        (case-match returns-thm
          ((!return-type (!fn . &))  (mv t return-type))
          ((('lambda r (!return-type r)) (!fn . &)) (mv t return-type))
          (('implies type-predicates (!return-type (!fn . formals)))
           (b* ((- (cw "type-predicates: ~q0"type-predicates))
                (- (cw "formals: ~q0" formals))
                (- (cw "actuals: ~q0" actuals))
                (- (cw "actuals judgements: ~q0" actuals-judgements))
                )
           (if (and (symbol-listp formals)
                    (path-cond-conj-implies-expr-list
                     actuals-judgements
                     (term-substitution-multi type-predicates formals actuals t)
                     state))
               (mv t return-type)
             (mv nil nil))))
          (& (mv nil nil))))
       ((unless ok)
        (er hard? 'type-inference=>construct-returns-judgement
            "The returns theorem for function ~p0 is of the wrong syntactic ~
               form ~p1~%" fn returns-thm)))
    `(if (,return-type (,fn ,@actuals)) 't 'nil)))
)

(local
 (defthm acl2-count-of-arg-decl-next->next
   (implies (and (not (equal (arg-decl-kind arg-decl) :done)))
            (< (acl2-count (arg-decl-next->next arg-decl))
               (acl2-count (arg-decl-fix arg-decl))))
   :hints (("Goal" :in-theory (enable arg-decl-fix arg-decl-next->next)))))

(defines returns-judgement
  :well-founded-relation l<
  :verify-guards nil

(define returns-judgement-single-arg ((fn symbolp)
                                      (actuals pseudo-term-listp)
                                      (actuals-total pseudo-term-listp)
                                      (actuals-judgements pseudo-termp)
                                      (actuals-judgements-total pseudo-termp)
                                      (arg-check arg-check-p)
                                      state)
  :returns (judgements pseudo-termp)
  :guard (and (consp actuals)
              (not (equal actuals-judgements ''t))
              (not (equal fn 'quote)))
  :measure (list (len (pseudo-term-list-fix actuals))
                 (acl2-count (arg-check-fix arg-check)))
  (b* (((unless (mbt (not (equal fn 'quote)))) nil)
       (actuals (pseudo-term-list-fix actuals))
       (actuals-judgements (pseudo-term-fix actuals-judgements))
       ((unless (is-conjunct? actuals-judgements))
        (er hard? 'type-inference=>returns-judgement-single-arg
            "Actuals judgements is not a conjunct ~p0.~%" actuals-judgements))
       (arg-check (arg-check-fix arg-check))
       ((unless (consp arg-check)) ''t)
       ((cons check-hd check-tl) arg-check)
       ((cons type arg-decl) check-hd)
       ((unless (mbt (and (consp actuals)
                          (not (equal actuals-judgements ''t)))))
        nil)
       ((cons actual actuals-tl) actuals)
       ((list & actual-judge actuals-judge-tl &) actuals-judgements)
       (guard-term `(,type ,actual))
       (- (cw "guard-term: ~q0" guard-term))
       (- (cw "actual-judge: ~q0" actual-judge))
       (yes? (path-cond-implies-expr-not-nil actual-judge guard-term state))
       ((unless yes?)
        (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
                                      actuals-judgements-total check-tl state)))
    (returns-judgement fn actuals-tl actuals-total
                       actuals-judge-tl actuals-judgements-total arg-decl state)))

(define returns-judgement ((fn symbolp)
                           (actuals pseudo-term-listp)
                           (actuals-total pseudo-term-listp)
                           (actuals-judgements pseudo-termp)
                           (actuals-judgements-total pseudo-termp)
                           (arg-decl arg-decl-p)
                           state)
  :returns (judgements pseudo-termp)
  :measure (list (len (pseudo-term-list-fix actuals))
                 (acl2-count (arg-decl-fix arg-decl)))
  :guard (not (equal fn 'quote))
  (b* (((unless (mbt (not (equal fn 'quote)))) nil)
       (actuals (pseudo-term-list-fix actuals))
       (actuals-judgements (pseudo-term-fix actuals-judgements))
       (arg-decl (arg-decl-fix arg-decl))
       ((if (and (equal (arg-decl-kind arg-decl) :done)
                 (null actuals)
                 (equal actuals-judgements ''t)))
        (progn$ (cw "fn: ~p0, actuals: ~p1~%" fn actuals)
               (cw "actuals-judgements-total: ~p0~%" actuals-judgements-total)
        (construct-returns-judgement fn actuals-total
                                     actuals-judgements-total
                                     (arg-decl-done->r arg-decl)
                                     state)))
       ((if (and (equal (arg-decl-kind arg-decl) :done)
                 (or actuals (not (equal actuals-judgements ''t)))))
        (er hard? 'type-inference=>returns-judgement
            "Run out of arg-decls.~%"))
       ((if (or (null actuals)
                (equal actuals-judgements ''t)))
        (er hard? 'type-inference=>returns-judgement
            "Run out of actuals or actuals-judgements.~%"))
       (arg-check (arg-decl-next->next arg-decl)))
    (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
                                  actuals-judgements-total arg-check state)))
)

(verify-guards returns-judgement
  :hints (("Goal"
           :in-theory (disable pseudo-termp))))

(encapsulate ()
  (local
   (in-theory (disable (:definition assoc-equal)
                       (:definition symbol-listp)
                       (:rewrite is-conjunct?-very-stupid)
                       (:rewrite lambda-of-pseudo-lambdap)
                       (:rewrite consp-of-pseudo-lambdap)
                       (:rewrite pseudo-term-listp-of-symbol-listp)
                       (:rewrite consp-of-cdr-of-pseudo-lambdap))))

(define strengthen-judgement-single ((judgement pseudo-termp)
                                     (path-cond pseudo-termp)
                                     (options type-options-p)
                                     state)
  :returns (new-judgement
            pseudo-termp
            :hints (("Goal"
                     :in-theory
                     (disable (:definition pseudo-termp)
                              (:rewrite
                               consp-of-pseudo-lambdap)
                              (:rewrite
                               acl2::pseudo-lambdap-of-car-when-pseudo-lambda-listp)
                              (:rewrite pseudo-term-listp-of-symbol-listp)
                              (:rewrite
                               acl2::symbol-listp-of-cdr-when-symbol-listp)
                              (:rewrite default-cdr)
                              (:rewrite acl2::pseudo-termp-opener)
                              (:rewrite equal-fixed-and-x-of-pseudo-termp)))))
  :ignore-ok t ;; for var
  (b* ((options (type-options-fix options))
       (judgement (pseudo-term-fix judgement))
       (- (cw "judgement: ~q0" judgement))
       (- (cw "path-cond: ~q0" path-cond))
       ((unless (type-predicate-p judgement (type-options->supertype options)))
        (er hard? 'type-inference=>strengthen-judgement
            "Judgement to be strengthened ~p0 is malformed.~%" judgement))
       (option-description (type-options->option options))
       ((list type term) judgement)
       (maybe-type? (is-maybe-type? type option-description))
       (- (cw "maybe-type?: ~q0" maybe-type?))
       ((unless maybe-type?) judgement)
       (not-nil?
        (path-cond-implies-expr-not-nil path-cond term state))
       (- (cw "non-nil?: ~q0" not-nil?))
       ((unless not-nil?) judgement)
       (nonnil-name
        (get-nonnil-thm type option-description))
       (nonnil-thm
        (acl2::meta-extract-formula-w nonnil-name (w state)))
       ((unless (pseudo-termp nonnil-thm))
        (er hard? 'type-inference=>strengthen-judgement
            "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
            nonnil-name nonnil-thm))
       (- (cw "non-nil-thm: ~q0" nonnil-thm))
       ((mv ok strengthened-type)
        (case-match nonnil-thm
          (('implies ('if (!type var) ('not ('null var)) ''nil)
                     (strengthened-type var))
           (mv t strengthened-type))
          (& (mv nil nil))))
       ((unless (and ok (symbolp strengthened-type)))
        (er hard? 'type-inference=>strengthen-judgement
            "The non-nil theorem for type ~p0 is of the wrong syntactic form ~
              ~p1~%" type nonnil-thm)))
    `(,strengthened-type ,term)))
)

(define strengthen-judgements ((judgements pseudo-termp)
                               (path-cond pseudo-termp)
                               (options type-options-p)
                               state)
  :returns (new-judgements pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judgements))
  (b* ((judgements (pseudo-term-fix judgements))
       ((unless (is-conjunct? judgements))
        (er hard? 'type-inference=>strengthen-judgements
            "~p0 is not a conjunction.~%" judgements))
       ((if (equal judgements ''t)) judgements)
       ((list* & judge-hd judge-tl &) judgements))
    `(if ,(strengthen-judgement-single judge-hd path-cond options state)
         ,(strengthen-judgements judge-tl path-cond options state)
       'nil)))

(encapsulate ()
  (local (in-theory (disable (:definition pseudo-termp)
                             (:definition assoc-equal)
                             (:definition symbol-listp)
                             (:rewrite lambda-of-pseudo-lambdap))))

(define check-nil-thm ((type symbolp)
                       (thm-name symbolp)
                       state)
  :returns (ok booleanp)
  (b* ((nil-thm
        (acl2::meta-extract-formula-w thm-name (w state)))
       ((unless (pseudo-termp nil-thm))
        (er hard? 'type-inference=>check-nil-thm
            "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
            thm-name nil-thm))
       (ok (case-match nil-thm
             ((!type ''nil) t)
             (& nil)))
       ((unless ok)
        (er hard? 'type-inference=>check-nil-thm
            "Nil theorem is malformed: ~q0" nil-thm)))
    t))

(define type-judgement-nil-list ((list list-type-description-alist-p)
                                 (acc pseudo-termp)
                                 state)
  :returns (judgements pseudo-termp)
  :measure (len (list-type-description-alist-fix list))
  (b* ((list (list-type-description-alist-fix list))
       (acc (pseudo-term-fix acc))
       ((unless (consp list)) acc)
       ((cons list-hd list-tl) list)
       ((cons type type-description) list-hd)
       (nil-thm (list-type-description->nil-thm type-description))
       (yes? (check-nil-thm type nil-thm state))
       ((unless yes?)
        (er hard? 'type-inference=>type-judgement-nil-list
            "list type ~p0 failed the nil-thm check.~%" type))
       (new-judge `(,type 'nil)))
    (type-judgement-nil-list list-tl `(if ,new-judge ,acc 'nil) state)))

(define type-judgement-nil-alist ((alist alist-type-description-alist-p)
                                  (acc pseudo-termp)
                                  state)
  :returns (judgements pseudo-termp)
  :measure (len (alist-type-description-alist-fix alist))
  (b* ((alist (alist-type-description-alist-fix alist))
       (acc (pseudo-term-fix acc))
       ((unless (consp alist)) acc)
       ((cons alist-hd alist-tl) alist)
       ((cons type type-description) alist-hd)
       (nil-thm (alist-type-description->nil-thm type-description))
       (yes? (check-nil-thm type nil-thm state))
       ((unless yes?)
        (er hard? 'type-inference=>type-judgement-nil-alist
            "alist type ~p0 failed the nil-thm check.~%" type))
       (new-judge `(,type 'nil)))
    (type-judgement-nil-alist alist-tl `(if ,new-judge ,acc 'nil) state)))

(define type-judgement-nil-option ((option option-type-description-alist-p)
                                   (acc pseudo-termp)
                                   state)
  :returns (judgements pseudo-termp)
  :measure (len (option-type-description-alist-fix option))
  (b* ((option (option-type-description-alist-fix option))
       (acc (pseudo-term-fix acc))
       ((unless (consp option)) acc)
       ((cons option-hd option-tl) option)
       ((cons type type-description) option-hd)
       (nil-thm (option-type-description->nil-thm type-description))
       (yes? (check-nil-thm type nil-thm state))
       ((unless yes?)
        (er hard? 'type-inference=>type-judgement-option
            "option type ~p0 failed the nil-thm check.~%" type))
       (new-judge `(,type 'nil)))
    (type-judgement-nil-option option-tl `(if ,new-judge ,acc 'nil) state)))
)

;; Add list type, alist type, option type
(define type-judgement-nil ((options type-options-p) state)
  :returns (judgements pseudo-termp)
  (b* ((options (type-options-fix options))
       (list (type-options->list options))
       (alist (type-options->alist options))
       (option (type-options->option options))
       (acc1 (type-judgement-nil-list list ''t state))
       (acc2 (type-judgement-nil-alist alist acc1 state))
       (acc3 (type-judgement-nil-option option acc2 state)))
    `(if (booleanp 'nil)
         (if (symbolp 'nil)
             ,acc3
           'nil)
       'nil)))

(define type-judgement-t ()
  :returns (judgements pseudo-termp)
  `(if (symbolp 't)
       (if (booleanp 't) 't 'nil)
     'nil))

(define type-judgement-quoted ((term pseudo-termp)
                               (options type-options-p)
                               state)
  :guard (and (not (acl2::variablep term))
              (acl2::fquotep term))
  :returns (judgements pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (options (type-options-fix options))
       ((unless (mbt (acl2::fquotep term))) nil)
       (const (cadr term))
       (supertype-alst (type-options->supertype options))
       (supertype-thm-alst (type-options->supertype-thm options)))
    (cond ((integerp const)
           (supertype-judgements `(if (integerp ',const) 't 'nil)
                                 supertype-alst supertype-thm-alst state))
          ((rationalp const)
           (supertype-judgements `(if (rationalp ',const) 't 'nil)
                                 supertype-alst supertype-thm-alst state))
          ((equal const t)
           (supertype-judgements (type-judgement-t)
                                 supertype-alst supertype-thm-alst state))
          ((null const) (type-judgement-nil options state))
          ((symbolp const)
           (supertype-judgements `(if (symbolp ',const) 't 'nil) supertype-alst
                                supertype-thm-alst state))
          (t (er hard? 'type-inference=>type-judgement-quoted
                 "Type inference for constant term ~p0 is not supported.~%"
                 term)))))

(local
 (defthm pseudo-termp-of-lambda
   (implies (and (symbol-listp formals)
                 (pseudo-termp body-judgements)
                 (pseudo-term-listp actuals)
                 (pseudo-termp substed-actuals-judgements)
                 (equal (len formals) (len actuals)))
            (pseudo-termp `((lambda ,formals
                              (if ,body-judgements
                                  ,substed-actuals-judgements
                                'nil))
                            ,@actuals))))
 )

(defines type-judgements
  :well-founded-relation l<
  :verify-guards nil
  :hints (("Goal"
           :in-theory (disable
                       (:definition pseudo-termp)
                       (:rewrite acl2::pseudo-term-listp-of-cons)
                       nth symbol-listp assoc-equal)))
  :returns-hints
  (("Goal"
    :in-theory (disable
                (:definition pseudo-termp)
                (:rewrite acl2::pseudo-term-listp-of-cons)
                nth symbol-listp assoc-equal)))

  (define type-judgement-lambda ((term pseudo-termp)
                                 (path-cond pseudo-termp)
                                 (options type-options-p)
                                 state)
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :guard (and (consp term)
                (pseudo-lambdap (car term)))
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         ((unless (mbt (and (consp term) (pseudo-lambdap (car term))))) nil)
         ((cons fn actuals) term)
         (formals (lambda-formals fn))
         (body (lambda-body fn))
         (shadowed-path-cond (shadow-path-cond formals path-cond))
         (body-judgements
          (type-judgement body shadowed-path-cond options state))
         (actuals-judgements
          (type-judgement-list actuals path-cond options state))
         (substed-actuals-judgements
          (term-substitution-multi actuals-judgements actuals formals t))
         (lambda-judgements
          `((lambda ,formals
              (if ,body-judgements
                  ,substed-actuals-judgements
                'nil))
            ,@actuals))
         (return-judgement
          (term-substitution (type-judgement-top body-judgements) body term t)))
      `(if ,return-judgement
           (if ,lambda-judgements
               ,actuals-judgements
             'nil)
         'nil)))

  (define type-judgement-if ((term pseudo-termp)
                             (path-cond pseudo-termp)
                             (options type-options-p)
                             state)
    :guard (and (consp term)
                (equal (car term) 'if))
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         ((unless (mbt (and (consp term) (equal (car term) 'if)))) nil)
         ((cons & actuals) term)
         ((unless (equal (len actuals) 3))
          (er hard? 'type-inference=>type-judgement-if
              "Mangled if term: ~q0" term))
         ((list cond then else) actuals)
         (- (cw "cond: ~p0, then: ~p1, else: ~p2~%" cond then else))
         (judge-cond (type-judgement cond path-cond options state))
         (judge-then (type-judgement then `(if ,cond ,path-cond 'nil) options state))
         (judge-else (type-judgement else `(if (not ,cond) ,path-cond 'nil)
                                     options state))
         (- (cw "judge-cond: ~p0, judge-then: ~p1, judge-else: ~p2~%"
                             judge-cond judge-then judge-else))
         (judge-then-top (type-judgement-top judge-then))
         (judge-else-top (type-judgement-top judge-else))
         (judge-from-then (term-substitution judge-then-top then term t))
         (judge-from-else (term-substitution judge-else-top else term t))
         (supertype-alst (type-options->supertype options))
         (supertype-thm-alst (type-options->supertype-thm options))
         (- (cw "judge-from-then: ~q0" judge-from-then))
         (- (cw "judge-from-else: ~q0" judge-from-else))
         (judge-if-top (union-judgements judge-from-then judge-from-else
                                         supertype-alst supertype-thm-alst
                                         state))
         (- (cw "judge-if-top: ~q0" judge-if-top))
         (judge-if-top-extended
          (supertype-judgements judge-if-top
                                supertype-alst supertype-thm-alst state)))
      `(if ,judge-if-top-extended
           (if ,judge-cond
               (if ,cond ,judge-then ,judge-else)
             'nil)
         'nil)))

  (define type-judgement-fn ((term pseudo-termp)
                             (path-cond pseudo-termp)
                             (options type-options-p)
                             state)
    :guard (and (consp term)
                (symbolp (car term))
                (not (equal (car term) 'if))
                (not (equal (car term) 'quote)))
    :measure (list (acl2-count (pseudo-term-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         (options (type-options-fix options))
         ((unless (mbt (and (consp term)
                            (symbolp (car term))
                            (not (equal (car term) 'quote))
                            (not (equal (car term) 'if)))))
          nil)
         ((cons fn actuals) term)
         ((if (is-type? fn (type-options->supertype options))) ''t)
         (actuals-judgements
          (type-judgement-list actuals path-cond options state))
         (actuals-judgements-top (type-judgement-top-list actuals-judgements))
         (functions (type-options->functions options))
         (conspair (assoc-equal fn functions))
         ((unless conspair)
          (er hard? 'type-inference=>type-judgement-fn
              "There exists no function description for function ~p0. ~%" fn))
         (fn-description (cdr conspair))
         (supertype-alst (type-options->supertype options))
         (supertype-thm-alst (type-options->supertype-thm options))
         (- (cw "fn: ~q0" fn))
         (- (cw "actuals: ~q0" actuals))
         (- (cw "actuals-judgements-top: ~q0" actuals-judgements-top))
         (weak-return-judgement
          (returns-judgement fn actuals actuals actuals-judgements-top
                             actuals-judgements-top fn-description state))
         (- (cw "weak-return-judgement: ~q0" weak-return-judgement))
         (return-judgement
          (strengthen-judgements weak-return-judgement path-cond options
                                 state))
         (- (cw "strengthened return-judgement: ~q0" return-judgement))
         (return-judgement-extended
          (supertype-judgements return-judgement supertype-alst
                                supertype-thm-alst state)))
      `(if ,return-judgement-extended
           ,actuals-judgements
         'nil)))

  (define type-judgement ((term pseudo-termp)
                          (path-cond pseudo-termp)
                          (options type-options-p)
                          state)
    :measure (list (acl2-count (pseudo-term-fix term)) 1)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         (options (type-options-fix options))
         ((if (acl2::variablep term))
          `(if ,(supertype-judgements
                 (look-up-path-cond term path-cond (type-options->supertype options))
                 (type-options->supertype options)
                 (type-options->supertype-thm options)
                 state)
               't 'nil))
         ((if (acl2::quotep term))
          `(if ,(type-judgement-quoted term options state)
               't 'nil))
         ((cons fn &) term)
         ((if (pseudo-lambdap fn))
          (type-judgement-lambda term path-cond options state))
         ((if (equal fn 'if))
          (type-judgement-if term path-cond options state)))
      (type-judgement-fn term path-cond options state)))

  (define type-judgement-list ((term-lst pseudo-term-listp)
                               (path-cond pseudo-termp)
                               (options type-options-p)
                               state)
    :measure (list (acl2-count (pseudo-term-list-fix term-lst)) 1)
    :returns (judgements-lst pseudo-termp)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (path-cond (pseudo-term-fix path-cond))
         ((unless (consp term-lst)) ''t)
         ((cons first rest) term-lst)
         (first-judge (type-judgement first path-cond options state))
         (rest-judge (type-judgement-list rest path-cond options state)))
      `(if ,first-judge
           ,rest-judge
         'nil)))
  )

(verify-guards type-judgement)

;; #|
;; test type-judgement

(defalist rational-integer-alist
  :key-type rationalp
  :val-type integerp
  :pred rational-integer-alistp
  :true-listp t)

(define rational-integer-cons-p ((x t))
  (and (consp x)
       (rationalp (car x))
       (integerp (cdr x))))

(easy-fix rational-integer-cons (cons 0 0))

(defoption maybe-integerp integerp :pred maybe-integerp)

(defoption maybe-rational-integer-consp rational-integer-cons-p
  :pred maybe-rational-integer-consp)

(defun supertype ()
  `((integerp . rationalp)
    (rationalp . nil)
    (symbolp . nil)
    (booleanp . nil)
    (rational-integer-cons-p . nil)
    (rational-integer-alistp . nil)
    (maybe-integerp . nil)
    (maybe-rational-integer-consp . nil)
    ))

(defthm integerp-implies-rationalp
  (implies (integerp x) (rationalp x)))

(defun supertype-thm ()
  `((,(make-type-tuple :type 'integerp :super-type 'rationalp) . integerp-implies-rationalp)))


(defthm return-of-assoc-equal
  (implies (rational-integer-alistp x)
           (maybe-rational-integer-consp (assoc-equal y x)))
  :hints (("Goal" :in-theory (enable maybe-rational-integer-consp
                                     rational-integer-cons-p))))

(defthm return-of-cdr-maybe
  (implies (maybe-rational-integer-consp x)
           (maybe-integerp (cdr x)))
  :hints (("Goal" :in-theory (enable maybe-rational-integer-consp
                                     rational-integer-cons-p))))

(defthm return-of-cdr
  (implies (rational-integer-cons-p x)
           (integerp (cdr x)))
  :hints (("Goal" :in-theory (enable rational-integer-cons-p))))

(defthm return-of-<
  (implies (and (integerp x)
                (integerp y))
           (booleanp (< x y))))

(defthm return-of-binary-+
  (implies (and (integerp x)
                (integerp y))
           (integerp (binary-+ x y))))

(defthm return-of-unary--
  (implies (integerp x)
           (integerp (unary-- x))))

;; assoc-equal: rational-integer-alistp -> maybe-rational-integer-consp
;; cdr: maybe-rational-integer-consp -> maybe-integerp &
;;      rational-integer-consp -> integerp
;; <: integerp integerp -> booleanp
;; binary-+: integerp integerp -> integerp
;; unary--: integerp -> integerp
(defun functions ()
  `((assoc-equal . ,(make-arg-decl-next
                     :next `((rationalp . ,(make-arg-decl-next
                                            :next `((rational-integer-alistp . ,(make-arg-decl-done
                                                                                 :r (make-return-spec
                                                                                     :return-type 'maybe-rational-integer-consp
                                                                                     :returns-thm 'return-of-assoc-equal)))))))))
    (cdr . ,(make-arg-decl-next
             :next `((maybe-rational-integer-consp . ,(make-arg-decl-done
                                                      :r (make-return-spec
                                                          :return-type 'maybe-integerp
                                                          :returns-thm 'return-of-cdr-maybe)))
                     (rational-integer-cons-p . ,(make-arg-decl-done
                                                 :r (make-return-spec
                                                     :return-type 'integerp
                                                     :returns-thm 'return-of-cdr))))))
    (< . ,(make-arg-decl-next
           :next `((integerp . ,(make-arg-decl-next
                                 :next `((integerp . ,(make-arg-decl-done
                                                       :r (make-return-spec
                                                           :return-type 'booleanp
                                                           :returns-thm 'return-of-<)))))))))
    (binary-+ . ,(make-arg-decl-next
                  :next `((integerp . ,(make-arg-decl-next
                                        :next `((integerp .
                                                          ,(make-arg-decl-done
                                                            :r (make-return-spec
                                                                :return-type 'integerp
                                                                :returns-thm 'return-of-binary-+)))))))))
    (unary-- . ,(make-arg-decl-next
                 :next `((integerp . ,(make-arg-decl-done
                                       :r (make-return-spec
                                           :return-type 'integerp
                                           :returns-thm 'return-of-unary--))))))))

(defun basic ()
  `((integerp . ,(make-basic-type-description :recognizer 'integerp
                                              :fixer 'ifix))
    (rationalp . ,(make-basic-type-description :recognizer 'rationalp
                                               :fixer 'rfix))
    (symbolp . ,(make-basic-type-description :recognizer 'symbolp
                                             :fixer 'symbol-fix))
    (booleanp . ,(make-basic-type-description :recognizer 'booleanp
                                             :fixer 'bool-fix))))

(defun consp-info ()
  `((rational-integer-cons-p . ,(make-cons-type-description :recognizer
                                                            'rational-integer-cons-p
                                                            :fixer
                                                            'rational-integer-cons-fix
                                                            :car-type 'rationalp
                                                            :cdr-type 'integerp
                                                            :cdr-thm nil))))

(defthm nil-thm-rational-integer-alistp
  (rational-integer-alistp nil))

(defun alist ()
  `((rational-integer-alistp . ,(make-alist-type-description :recognizer 'rational-integer-alistp
                                                             :fixer 'rational-integer-alist-fix
                                                             :key-type 'rationalp
                                                             :val-type 'integerp
                                                             :acons-thm nil
                                                             :assoc-equal-thm nil
                                                             :nil-thm 'nil-thm-rational-integer-alistp
                                                             ))))

(defthm nil-thm-maybe-rational-integer-consp
  (maybe-rational-integer-consp nil))

(defthm non-nil-thm-maybe-rational-integer-consp
  (implies (and (maybe-rational-integer-consp x)
                (not (null x)))
           (rational-integer-cons-p x)))

(defthm nil-thm-maybe-integerp
  (maybe-integerp nil))

(defthm non-nil-thm-maybe-integerp
  (implies (and (maybe-integerp x)
                (not (null x)))
           (integerp x)))

(defun option ()
  `((maybe-integerp . ,(make-option-type-description :recognizer
                                                     'maybe-integerp
                                                     :fixer 'maybe-integer-fix
                                                     :some-type 'integerp
                                                     :some-constructor-thm nil
                                                     :none-constructor-thm nil
                                                     :some-destructor-thm nil
                                                     :non-nil-thm 'non-nil-thm-maybe-integerp
                                                     :nil-thm 'nil-thm-maybe-integerp
                                                     ))
    (maybe-rational-integer-consp . ,(make-option-type-description :recognizer 'maybe-rational-integer-consp
                                                                   :fixer 'maybe-rational-integer-cons-fix
                                                                   :some-type
                                                                   'rational-integer-cons-p
                                                                   :some-constructor-thm nil
                                                                   :none-constructor-thm nil
                                                                   :some-destructor-thm nil
                                                                   :non-nil-thm 'non-nil-thm-maybe-rational-integer-consp
                                                                   :nil-thm 'nil-thm-maybe-rational-integer-consp
                                                                   ))))

(defun options ()
  (b* ((supertype (supertype))
       (supertype-thm (supertype-thm))
       (functions (functions))
       (basic (basic))
       (consp (consp-info))
       (list nil)
       (alist (alist))
       (prod nil)
       (option (option))
       (sum nil)
       (abstract nil))
    (make-type-options
     :supertype supertype
     :supertype-thm supertype-thm
     :functions functions
     :basic basic
     :consp consp
     :list list
     :alist alist
     :prod prod
     :option option
     :sum sum
     :abstract abstract)))

(defun term ()
  '(if (if (rational-integer-alistp al)
           (if (rationalp r1)
               (assoc-equal r1 al)
             'nil)
         'nil)
       (< (binary-+ (cdr (assoc-equal r1 al))
                    (unary-- (cdr (assoc-equal r1 al))))
          '2)
     't))

(type-judgement (term) ''t (options) state)
stop
;; |#

(define type-judge-fn ((cl pseudo-term-listp)
                       (smtlink-hint t)
                       state)
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint))
        (list cl))
       ((smtlink-hint h) smtlink-hint)
       (goal (disjoin cl))
       (options (construct-type-options smtlink-hint)) ;; TODO
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
   (implies (and (ev-infer-meta-extract-global-facts)
                 (pseudo-term-listp cl)
                 (alistp a)
                 (ev-infer
                  (conjoin-clauses
                   (acl2::clauses-result
                    (type-judge-cp cl hint state)))
                  a))
            (ev-infer (disjoin cl) a))
   :rule-classes :clause-processor)
 )
