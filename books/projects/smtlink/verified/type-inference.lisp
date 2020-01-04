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

(fty::deftypes function-description
  (deftagsum arg-decl
    (:next ((next arg-check-p)))
    (:done ((r return-spec-p))))
  (defalist arg-check
    :key-type symbolp
    :val-type arg-decl-p))

(defprod list-type-description
  ((recognizer symbolp)
   (elt-type symbolp)
   (cons-thm symbolp)
   (car-thm symbolp)
   (cdr-thm symbolp)
   (true-list-thm symbolp)))

(defprod alist-type-description
  ((recognizer symbolp)
   (key-type symbolp)
   (val-type symbolp)
   (acons-thm symbolp)
   (assoc-equal-thm symbolp)
   (true-list-thm symbolp)))

(defprod prod-type-description
  ((recognizer symbolp)
   (field-types symbol-listp)
   (constructor-thm symbolp)
   (destructor-thms symbol-listp)))

(defprod option-type-description
  ((recognizer symbolp)
   (some-type symbolp)
   (some-constructor-thm symbolp)
   (none-constructor-thm symbolp)
   (some-destructor-thm symbolp)))

(defprod sum-type-description
  ((prod-list prod-type-description-p)))

(defprod abstract-type-description
  ((recognizer symbolp)))

;; For some reason, this one takes a while
(defprod type-options
  ((supertype type-to-supertype-alist-p)
   (supertype-thm type-tuple-to-thm-alist-p)
   (functions arg-check-p)
   (list list-type-description-p)
   (alist alist-type-description-p)
   (prod prod-type-description-p)
   (option option-type-description-p)
   (sum sum-type-description-p)
   (abstract abstract-type-description-p)))

(define is-maybe-type? ((type symbolp)
                        (options type-options-p))
  :returns (ok booleanp)
  :irrelevant-formals-ok t
  :ignore-ok t
  nil)

(define get-nonnil-thm ((type symbolp)
                        (options type-options-p))
  :returns (thm pseudo-termp)
  :irrelevant-formals-ok t
  :ignore-ok t
  nil)

(define get-returns-thm ((fn symbolp)
                         (options type-options-p))
  :returns (thm pseudo-termp)
  :irrelevant-formals-ok t
  :ignore-ok t
  nil)

;; ----------------------------------------------------------------
;;       Subtyping

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
       ((unless conspair) nil))
    (cons (cdr conspair)
          (supertype-clocked (cdr conspair) supertype-alst (1- clock)))))

;; -----------------------------------------------------

(define supertype-to-judgements ((supertypes symbol-listp)
                                 (term pseudo-termp))
  :returns (judgements pseudo-termp)
  :measure (len supertypes)
  (b* ((supertypes (symbol-list-fix supertypes))
       (term (pseudo-term-fix term))
       ((unless (consp supertypes)) 't)
       ((cons supertypes-hd supertypes-tl) supertypes))
    `(if (,supertypes-hd ,term)
         ,(supertype-to-judgements supertypes-tl term)
       'nil)))

(define supertype-judgement ((type-judgement pseudo-termp)
                             (supertype-alst
                              type-to-supertype-alist-p))
  :returns (judgements pseudo-termp)
  (b* ((root-type (symbol-fix root-type))
       (supertype-alst (type-to-supertype-alist-fix supertype-alst))
       (clock (len supertype-alst))
       (supertypes
        (supertype-clocked root-type supertype-alst clock)))
    (supertype-to-judgements supertypes term)))

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

(define is-conjunct? ((term pseudo-termp))
  :returns (ok booleanp)
  (b* ((term (pseudo-term-fix term)))
    (implies (not (equal term 't))
             (and (consp term)
                  (equal (car term) 'if)
                  (equal (len term) 4)
                  (equal (cadddr term) 'nil))))
  ///
  (more-returns
   (ok (implies (and ok (pseudo-termp term) (not (equal term 't)))
                (and (consp term)
                     (pseudo-termp (cadr term))
                     (pseudo-termp (caddr term))))
       :name implies-of-is-conjunct?)
   (ok (implies (and ok (pseudo-termp term) (not (equal term 't)))
                (< (acl2-count (caddr term))
                   (acl2-count term)))
       :name acl2-count-of-caddr-of-is-conjunct?
       :hints (("Goal"
                :in-theory (disable implies-of-is-conjunct?
                                    symbol-listp)))
       :rule-classes :linear)))

(define path-cond-implies-expr ((path-cond pseudo-termp)
                                (expr pseudo-termp)
                                state)
  :returns (ok booleanp)
  :measure (acl2-count (pseudo-term-fix path-cond))
  (b* ((path-cond (pseudo-term-fix path-cond))
       (expr (pseudo-term-fix expr))
       ((unless (is-conjunct? path-cond))
        (er hard? 'type-inference=>path-cond-implies-expr
            "Path condition is not a conjunction of conditions: ~q0" path-cond))
       ((if (equal path-cond 't)) nil)
       ((list* & path-hd path-tl &) path-cond)
       (path-hd-nil/expr (term-substitution path-hd expr 'nil))
       ((if (null (eval-const-expr path-hd-nil/expr state))) t))
    (path-cond-implies-expr path-tl expr state)))

(define look-up-path-cond ((term pseudo-termp)
                           (path-cond pseudo-termp))
  :returns (type-term
            pseudo-termp
            :hints (("Goal" :in-theory (disable symbol-listp))))
  :measure (acl2-count (pseudo-term-fix path-cond))
  (b* ((term (pseudo-term-fix term))
       (path-cond (pseudo-term-fix path-cond))
       ((unless (is-conjunct? path-cond))
        (er hard? 'type-inference=>look-up-path-cond
            "Path condition is not a conjunction of conditions: ~q0" path-cond))
       ((if (equal path-cond 't)) 't)
       ((list* & path-hd path-tl &) path-cond)
       ((unless (and (equal (len path-hd) 2)
                     (equal (cadr path-hd) term)))
        (look-up-path-cond term path-tl)))
    `(if ,path-hd
         ,(look-up-path-cond term path-tl)
       'nil)))

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
       ((if (equal path-cond 't)) 't)
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
       ((if (equal judgements 't))
        (er hard? 'type-inference=>type-judgement-top
            "The judgements is empty.~%")))
    (cadr judgements)))

(define intersect-judgements ((judge1 pseudo-termp)
                              (judge2 pseudo-termp)
                              (thms type-tuple-to-thm-alist))
  :returns (intersection pseudo-termp)
  (b* ((judge1 (pseudo-term-fix judge1))
       (judge2 (pseudo-term-fix judge2))
       (thms (type-tuple-to-thm-alist thms))
       ()
       )
    ()))

(define strengthen-judgement ((judgement pseudo-termp)
                              (path-cond pseudo-termp)
                              (options type-options-p)
                              state)
  :returns (new-judgement pseudo-termp)
  :ignore-ok t ;; for var
  (b* ((judgement (pseudo-term-fix judgement))
       ((unless (and (equal (len judgement) 2)
                     (symbolp (car judgement))))
        (er hard? 'type-inference=>strengthen-judgement
            "Judgement to be strengthened ~p0 is malformed.~%" judgement))
       ((cons type term) judgement)
       (maybe-type? (is-maybe-type? type options))
       ((unless maybe-type?) judgement)
       (not-nil?
        (path-cond-implies-expr path-cond judgement state))
       ((unless not-nil?) judgement)
       (nonnil-name (get-nonnil-thm type options))
       (nonnil-thm
        (acl2::meta-extract-formula-w nonnil-name (w state)))
       ((unless (pseudo-termp nonnil-thm))
        (er hard? 'type-inference=>strengthen-judgement
            "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
            nonnil-name nonnil-thm))
       ((mv ok strengthened-type)
        (case-match nonnil-thm
          (('implies ('and (!type var) ('not ('null var)))
                     (strengthened-type var))
           (mv t strengthened-type))
          (& (mv nil nil))))
       ((unless ok)
        (er hard? 'type-inference=>strengthen-judgement
            "The non-nil theorem for type ~p0 is of the wrong syntactic form ~
              ~p1~%" type nonnil-thm)))
    `(,strengthened-type ,term)))

;; TODO
(define type-judgement-nil ((options type-options-p))
  :returns (judgements pseudo-termp)
  :irrelevant-formals-ok t
  :ignore-ok t
  `(if (booleanp nil)
       (if (symbolp nil)
           't
         'nil)))

(define type-judgement-quoted ((term pseudo-termp)
                               (options type-options-p))
  :guard (and (not (acl2::variablep term))
              (acl2::fquotep term))
  :returns (judgements pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       ((unless (mbt (acl2::fquotep term))) nil)
       (const (cadr term)))
    (cond ((integerp const) `(integerp ',const))
          ((rationalp const) `(rationalp ',const))
          ((null const) (type-judgement-nil options))
          ((booleanp const) `(booleanp ',const))
          ((symbolp const) `(symbolp ',const))
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
          (term-substitution-multi actuals-judgements actuals formals))
         (lambda-judgements
          `((lambda ,formals
              (if ,body-judgements
                  ,substed-actuals-judgements
                'nil))
            ,@actuals))
         (return-judgement
          (term-substitution (type-judgement-top body-judgements) body term)))
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
         ((list cond then else) term)
         (judge-cond (type-judgement cond path-cond options state))
         (judge-then (type-judgement then path-cond options state))
         (judge-else (type-judgement else path-cond options state))
         (judge-then-top (type-judgement-top judge-then))
         (judge-else-top (type-judgement-top judge-else))
         (judge-if-top (term-substitution judge-then-top then term))
         ((unless (equal judge-if-top
                         (term-substitution judge-else-top else term)))
          (er hard? 'type-inference=>type-judgement-if
              "Inconsistent type for then expression ~p0 and else expression ~
               ~p1~%" then else)))
      `(if ,judge-if-top
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
         ((unless (mbt (and (consp term)
                            (symbolp (car term))
                            (not (equal (car term) 'quote))
                            (not (equal (car term) 'if)))))
          nil)
         ((cons fn actuals) term)
         (actuals-judgements
          (type-judgement-list actuals path-cond options state))
         (returns-name (get-returns-thm fn options))
         (returns-thm
          (acl2::meta-extract-formula-w returns-name (w state)))
         ((unless (pseudo-termp returns-thm))
          (er hard? 'type-inference=>type-judgement-fn
              "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
              returns-name returns-thm))
         ((mv ok type)
          (case-match returns-thm
            ((type (!fn . &))  (mv t type))
            (& (mv nil nil))))
         ((unless ok)
          (er hard? 'type-inference=>type-judgement-fn
              "The returns theorem for function ~p0 is of the wrong syntactic ~
               form ~p1~%" fn returns-thm))
         (weak-return-judgement `(,type ,term))
         (return-judgement
          (strengthen-judgement weak-return-judgement path-cond options
                                state)))
      `(if ,return-judgement
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
         ((if (acl2::variablep term))
          (look-up-path-cond term path-cond))
         ((if (acl2::quotep term))
          (type-judgement-quoted term options))
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
         ((unless (consp term-lst)) 't)
         ((cons first rest) term-lst)
         (first-judge (type-judgement first path-cond options state))
         (rest-judge (type-judgement-list rest path-cond options state)))
      `(if ,first-judge
           ,rest-judge
         'nil)))
  )

(verify-guards type-judgement)

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
       (type-judgements (type-judgement goal 't options state))
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
