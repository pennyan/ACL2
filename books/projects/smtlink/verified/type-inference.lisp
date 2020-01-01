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

(define look-up-type-judgement ((term pseudo-termp)
                                  (judgements pseudo-termp)
                                  (acc pseudo-termp))
    :returns (judgement pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (judgements (pseudo-term-fix judgements))
         (acc (pseudo-term-fix acc))
         ((if (or (acl2::quotep judgements)
                  (acl2::variablep judgements)))
          acc)
         ((cons fn actuals) judgements)
         ((if (pseudo-lambdap fn)) acc)
         ;; TODO: doesn't allow type judgement like (< x '0) to be found
         ((if (and (not (equal fn 'if))
                   (equal (len actuals) 1)
                   (equal (car actuals) term)))
          `(if ,judgements ,acc 'nil))
         ((unless (equal fn 'if)) acc)
         ((if (not (equal (len actuals) 3)))
          (er hard? 'type-inference=>look-up-type-judgement
              "Wrong if statement: ~q0" judgements))
         ((unless (equal (cddr actuals) 'nil)) acc))
    (look-up-type-judgement term (cadr actuals) acc)))

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
                                 (smtlink-hint smtlink-hint-p))
    :measure (list (acl2-count (pseudo-term-list-fix term)) 1)
    :guard (and (consp term)
                (pseudo-lambdap (car term)))
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         ((unless (mbt (and (consp term) (pseudo-lambdap (car term))))) nil)
         ((cons fn actuals) term)
         (formals (lambda-formals fn))
         (body (lambda-body fn))
         
         )
      ())
    )

  (define type-judgement-fncall ((term pseudo-termp)
                                 (path-cond pseudo-termp)
                                 (smtlink-hint smtlink-hint-p))
    :measure (list (acl2-count (pseudo-term-list-fix term)) 1)
    :guard (and (consp term)
                (symbolp (car term)))
    :returns (judgements pseudo-termp)
    :irrelevant-formals-ok t
    :ignore-ok t
    't)

  (define type-judgement ((term pseudo-termp)
                          (path-cond pseudo-termp)
                          (smtlink-hint smtlink-hint-p))
    :measure (list (acl2-count (pseudo-term-list-fix term)) 0)
    :returns (judgements pseudo-termp)
    (b* ((term (pseudo-term-fix term))
         (path-cond (pseudo-term-fix path-cond))
         ((if (acl2::variablep term))
          (look-up-path-cond term path-cond))
         ((if (acl2::quotep term))
          (type-judgement-quoted term smtlink-hint))
         ((cons fn &) term)
         ((if (pseudo-lambdap fn))
          (type-judgement-lambda term path-cond smtlink-hint)))
      (type-judgement-fncall term path-cond smtlink-hint)))

  (define type-judgement-list ((term-lst pseudo-term-listp)
                               (path-cond pseudo-termp)
                               (smtlink-hint smtlink-hint-p))
    :measure (list (acl2-count (pseudo-term-list-fix term-lst)) 0)
    :returns (judgements-lst pseudo-termp)
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (path-cond (pseudo-term-fix path-cond))
         ((unless (consp term-lst)) 't)
         ((cons first rest) term-lst)
         (first-judge (type-judgement first path-cond smtlink-hint))
         (rest-judge (type-judgement-list rest path-cond smtlink-hint)))
      `(if ,first-judge
           ,rest-judge
         'nil)))
  )
