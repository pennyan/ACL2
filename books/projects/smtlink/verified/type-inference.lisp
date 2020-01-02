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
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "hint-please")
(include-book "term-substitution")

(define is-maybe-type? ((type symbolp)
                        (smtlink-hint smtlink-hint-p))
  :returns (ok booleanp)
  :irrelevant-formals-ok t
  :ignore-ok t
  nil)

(define get-nonnil-thm ((type symbolp)
                        (smtlink-hint smtlink-hint-p))
  :returns (thm pseudo-termp)
  :irrelevant-formals-ok t
  :ignore-ok t
  nil)

(define get-returns-thm ((fn symbolp)
                         (smtlink-hint smtlink-hint-p))
  :returns (thm pseudo-termp)
  :irrelevant-formals-ok t
  :ignore-ok t
  nil)

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

(define strengthen-judgement ((judgement pseudo-termp)
                              (path-cond pseudo-termp)
                              (smtlink-hint smtlink-hint-p)
                              state)
  :returns (new-judgement pseudo-termp)
  :ignore-ok t ;; for var
  (b* ((judgement (pseudo-term-fix judgement))
       ((unless (and (equal (len judgement) 2)
                     (symbolp (car judgement))))
        (er hard? 'type-inference=>strengthen-judgement
            "Judgement to be strengthened ~p0 is malformed.~%" judgement))
       ((cons type term) judgement)
       (maybe-type? (is-maybe-type? type smtlink-hint))
       ((unless maybe-type?) judgement)
       (not-nil?
        (path-cond-implies-expr path-cond judgement state))
       ((unless not-nil?) judgement)
       (nonnil-name (get-nonnil-thm type smtlink-hint))
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
(define type-judgement-nil ((smtlink-hint smtlink-hint-p))
  :returns (judgements pseudo-termp)
  :irrelevant-formals-ok t
  :ignore-ok t
  `(if (booleanp nil)
       (if (symbolp nil)
           't
         'nil)))

(define type-judgement-quoted ((term pseudo-termp)
                               (smtlink-hint smtlink-hint-p))
  :guard (and (not (acl2::variablep term))
              (acl2::fquotep term))
  :returns (judgements pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       ((unless (mbt (acl2::fquotep term))) nil)
       (const (cadr term)))
    (cond ((integerp const) `(integerp ',const))
          ((rationalp const) `(rationalp ',const))
          ((null const) (type-judgement-nil smtlink-hint))
          ((booleanp const) `(booleanp ',const))
          ((symbolp const) `(symbolp ',const))
          (t (er hard? 'type-inference=>type-judgement-quoted
                 "Type inference for constant term ~p0 is not supported.~%"
                 term)))))

(defines type-judgements
  :well-founded-relation l<
  :verify-guards nil

  (define type-judgement-lambda ((term pseudo-termp)
                                 (path-cond pseudo-termp)
                                 (smtlink-hint smtlink-hint-p)
                                 state)
    :measure (list (acl2-count (pseudo-term-list-fix term)) 0)
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
          (type-judgement body shadowed-path-cond smtlink-hint state))
         (actuals-judgements
          (type-judgement-list actuals path-cond smtlink-hint state))
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
                             (smtlink-hint smtlink-hint-p)
                             state)
    :guard (and (consp term)
                (equal (car term) 'if))
    :measure (list (acl2-count (pseudo-term-list-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         ((unless (mbt (and (consp term) (equal (car term) 'if)))) nil)
         ((cons & actuals) term)
         ((unless (equal (len actuals) 3))
          (er hard? 'type-inference=>type-judgement-if
              "Mangled if term: ~q0" term))
         ((list cond then else) term)
         (judge-cond (type-judgement cond path-cond smtlink-hint state))
         (judge-then (type-judgement then path-cond smtlink-hint state))
         (judge-else (type-judgement else path-cond smtlink-hint state))
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
                             (smtlink-hint smtlink-hint-p)
                             state)
    :guard (and (consp term)
                (not (equal (car term) 'if)))
    :measure (list (acl2-count (pseudo-term-list-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         ((unless (mbt (and (consp term) (not (equal (car term) 'if))))) nil)
         ((cons fn actuals) term)
         (actuals-judgements
          (type-judgement-list actuals path-cond smtlink-hint state))
         (returns-name (get-returns-thm fn smtlink-hint))
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
          (strengthen-judgement weak-return-judgement path-cond smtlink-hint
                                state)))
      `(if ,return-judgement
           ,actuals-judgements
         'nil)))

  (define type-judgement ((term pseudo-termp)
                          (path-cond pseudo-termp)
                          (smtlink-hint smtlink-hint-p)
                          state)
    :measure (list (acl2-count (pseudo-term-list-fix term)) 1)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         ((if (acl2::variablep term))
          (look-up-path-cond term path-cond))
         ((if (acl2::quotep term))
          (type-judgement-quoted term smtlink-hint))
         ((cons fn &) term)
         ((if (pseudo-lambdap fn))
          (type-judgement-lambda term path-cond smtlink-hint state))
         ((if (equal fn 'if))
          (type-judgement-if term path-cond smtlink-hint state)))
      (type-judgement-fn term path-cond smtlink-hint state)))

  (define type-judgement-list ((term-lst pseudo-term-listp)
                               (path-cond pseudo-termp)
                               (smtlink-hint smtlink-hint-p)
                               state)
    :measure (list (acl2-count (pseudo-term-list-fix term-lst)) 1)
    :returns (judgements-lst pseudo-termp)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (path-cond (pseudo-term-fix path-cond))
         ((unless (consp term-lst)) 't)
         ((cons first rest) term-lst)
         (first-judge (type-judgement first path-cond smtlink-hint state))
         (rest-judge (type-judgement-list rest path-cond smtlink-hint state)))
      `(if ,first-judge
           ,rest-judge
         'nil)))
  )

(verify-guards type-judgements)
