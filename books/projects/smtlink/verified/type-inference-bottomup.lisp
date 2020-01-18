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
(include-book "partial-eval")
(include-book "judgements")
(include-book "evaluator")

(set-state-ok t)

;; -------------------------------------------------------------------
;;        Functions about path-cond

(define path-test ((path-cond pseudo-termp)
                   (expr pseudo-termp)
                   state)
  :returns (ok booleanp)
  (b* ((path-cond (pseudo-term-fix path-cond))
       (expr (pseudo-term-fix expr))
       (substed-cond (term-substitution path-cond expr ''nil t))
       ((mv err eval-cond) (partial-eval substed-cond nil state))
       ((if err) nil)
       ((unless eval-cond) t))
    nil))

(define path-test-list ((path-cond pseudo-termp)
                        (expr-conj pseudo-termp)
                        state)
  :returns (ok booleanp)
  :measure (acl2-count (pseudo-term-fix expr-conj))
  (b* ((path-cond (pseudo-term-fix path-cond))
       (expr-conj (pseudo-term-fix expr-conj))
       ((unless (is-conjunct? expr-conj))
        (path-test path-cond expr-conj state))
       ((if (equal expr-conj ''t)) t)
       ((list & expr-hd expr-tl &) expr-conj)
       (yes? (path-test path-cond expr-hd state))
       ((if yes?) (path-test-list path-cond expr-tl state)))
    nil))

#|
(path-test-list '(if (integerp x) (if (null x) 't 'nil) 'nil)
                '(if (integerp x) 't 'nil)
                state)
(path-test-list '(if (integerp x) (if (null x) 't 'nil) 'nil)
                '(if (rationalp x) 't 'nil)
                state)
(path-test-list '(if (integerp x) (if (null x) 't 'nil) 'nil)
                '(if x 't 'nil)
                state)
(path-test-list '(if (if (integerp x)
                         (if (null x) 't 'nil) 'nil)
                     (rationalp x)
                   'nil)
                '(if x (if (integerp x) 't 'nil) 'nil)
                state)
(path-test-list '(IF (IF (RATIONALP R1) 'T 'NIL)
                     (IF (IF (RATIONAL-INTEGER-ALISTP AL)
                             'T
                             'NIL)
                         'T
                         'NIL)
                     'NIL)
                '(rational-integer-alistp al)
                state)
|#

;; look-up-path-cond will ignore the whole branch of or's and only look for top
;; level and's
(define look-up-path-cond-acc ((term pseudo-termp)
                               (path-cond pseudo-termp)
                               (supertype-alst type-to-types-alist-p)
                               (acc pseudo-termp))
  :returns (type-term pseudo-termp)
  :measure (acl2-count (pseudo-term-fix path-cond))
  :verify-guards nil
  (b* ((term (pseudo-term-fix term))
       (path-cond (pseudo-term-fix path-cond))
       (acc (pseudo-term-fix acc))
       ((if (judgement-of-term path-cond term supertype-alst))
        `(if ,path-cond ,acc 'nil))
       ((unless (is-conjunct? path-cond)) acc)
       ((if (equal path-cond ''t)) acc)
       ((list* & path-hd path-tl &) path-cond)
       (new-acc (look-up-path-cond-acc term path-hd supertype-alst acc)))
    (look-up-path-cond-acc term path-tl supertype-alst new-acc)))

(verify-guards look-up-path-cond-acc)

(define look-up-path-cond ((term pseudo-termp)
                           (path-cond pseudo-termp)
                           (supertype-alst type-to-types-alist-p))
  :returns (type-term pseudo-termp)
  (look-up-path-cond-acc term path-cond supertype-alst ''t))

#|
(look-up-path-cond 'r1
                   '(if (if (rational-integer-alistp al)
                            (if (rationalp r1)
                                (assoc-equal r1 al)
                              'nil)
                          'nil)
                        't
                      'nil)
                   '((integerp . rationalp)
                     (rationalp)
                     (rational-integer-alistp)))

(look-up-path-cond 'r1
                   '(if (if (< r1 '0)
                            (if (rationalp r1)
                                (assoc-equal r1 al)
                              'nil)
                          'nil)
                        't
                      'nil)
                   '((integerp . rationalp)
                     (rationalp)))

(look-up-path-cond 'x
                   '(if (if x
                            (if (maybe-integerp x)
                                't
                              'nil)
                          'nil)
                        't
                      'nil)
                   '((integerp . rationalp)
                     (rationalp)
                     (maybe-integerp)))

(look-up-path-cond 'x
                   '(if (if (not x)
                            (if (maybe-integerp x)
                                't
                              'nil)
                          'nil)
                        't
                      'nil)
                   '((integerp . rationalp)
                     (rationalp)
                     (maybe-integerp)))

(look-up-path-cond 'x
                   '(if (not x)
                        (if x 't (if (maybe-integerp x) 't 'nil))
                      'nil)
                   '((integerp . rationalp)
                     (rationalp)
                     (maybe-integerp)))
|#

;; shadow-path-cond-acc will shadow the whole or branch if it contains
;; variables shadowed by formals.
(define shadow-path-cond-acc ((formals symbol-listp)
                              (path-cond pseudo-termp)
                              (acc pseudo-termp))
  :returns (shadowed-path-cond pseudo-termp)
  :measure (acl2-count (pseudo-term-fix path-cond))
  :verify-guards nil
  (b* ((formals (symbol-list-fix formals))
       (path-cond (pseudo-term-fix path-cond))
       (acc (pseudo-term-fix acc))
       ((if (and (not (is-conjunct? path-cond))
                 (dumb-occur-vars-or formals path-cond)))
        acc)
       ((unless (is-conjunct? path-cond))
        `(if ,path-cond ,acc 'nil))
       ((if (equal path-cond ''t)) acc)
       ((list* & path-hd path-tl &) path-cond)
       (new-acc (shadow-path-cond-acc formals path-hd acc)))
    (shadow-path-cond-acc formals path-tl new-acc)))

(verify-guards shadow-path-cond-acc)

(define shadow-path-cond ((formals symbol-listp)
                          (path-cond pseudo-termp))
  :returns (shadowed-path-cond pseudo-termp)
  (shadow-path-cond-acc formals path-cond ''t))

#|
(shadow-path-cond '(x)
                  '(if (not x) (if x 't (if (maybe-integerp x) 't nil))))

(shadow-path-cond '(x)
                  '(if (if (not x)
                           (if (maybe-integerp x)
                               't 'nil)
                         'nil)
                       't 'nil))

(shadow-path-cond '(x)
                  '(if (if (not x)
                           (if (maybe-integerp x)
                               't 'nil)
                         'nil)
                       (if (< '0 y)
                           (if (rationalp z) 't 'nil)
                         'nil)
                     'nil))
|#

;; ------------------------------------------------------------
;; Return the topest judgement

(define type-judgement-top ((judgements pseudo-termp)
                            (term pseudo-termp)
                            (options type-options-p))
  :returns (judgement pseudo-termp)
  (b* ((judgements (pseudo-term-fix judgements))
       (options (type-options-fix options))
       (supertype-alst (type-options->supertype options)))
    (look-up-path-cond term judgements supertype-alst)))

(define type-judgement-top-list ((judgements-lst pseudo-termp)
                                 (term-lst pseudo-term-listp)
                                 (options type-options-p))
  :returns (judgement-lst pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judgements-lst))
  (b* ((judgements-lst (pseudo-term-fix judgements-lst))
       (term-lst (pseudo-term-list-fix term-lst))
       ((unless (is-conjunct? judgements-lst))
        (er hard? 'type-inference-bottomup=>type-judgement-top-list
            "The top of type judgement is not a conjunction of conditions: ~q0"
            judgements-lst))
       ((if (or (equal judgements-lst ''t) (null term-lst))) ''t)
       ((list & judgements-hd judgements-tl &) judgements-lst)
       ((cons term-hd term-tl) term-lst))
    `(if ,(type-judgement-top judgements-hd term-hd options)
         ,(type-judgement-top-list judgements-tl term-tl options)
       'nil)))

;;-------------------------------------------------------
;;  Union judgements
(define union-judgements-acc ((judge1 pseudo-termp)
                              (judge2 pseudo-termp)
                              (acc pseudo-termp)
                              state)
  :returns (union pseudo-termp)
  :verify-guards nil
  :measure (acl2-count (pseudo-term-fix judge2))
  (b* ((judge1 (pseudo-term-fix judge1))
       (judge2 (pseudo-term-fix judge2))
       (acc (pseudo-term-fix acc))
       ((if (path-test judge1 judge2 state))
        `(if ,judge2 ,acc 'nil))
       ((unless (is-conjunct? judge2)) acc)
       ((if (equal judge2 ''t)) acc)
       ((list & judge-hd judge-tl &) judge2)
       (acc-hd (union-judgements-acc judge1 judge-hd acc state)))
    (union-judgements-acc judge1 judge-tl acc-hd state)))

(verify-guards union-judgements-acc)

(define union-judgements ((judge1 pseudo-termp)
                          (judge2 pseudo-termp)
                          state)
  :returns (union pseudo-termp)
  (union-judgements-acc judge1 judge2 ''t state))

#|
(defthm test (implies (integerp x) (rationalp x)))
(union-judgements '(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
                  '(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
                  state)

(union-judgements '(if (rationalp x) 't 'nil)
                  '(if (rationalp x) (if (integerp x) 't 'nil) 'nil)
                  state)
|#

;;-------------------------------------------------------
;; Super/subtype judgements

(defines super/subtype-transitive-closure
  :well-founded-relation l<
  :verify-guards nil

  (define super/subtype ((type symbolp)
                         (type-alst type-to-types-alist-p)
                         (closure symbol-listp)
                         (clock natp)) ;; clock is the length of the supertype-alst
    :measure (list (nfix clock) (acl2-count (symbol-fix type)))
    :returns (closure symbol-listp)
    (b* ((type (symbol-fix type))
         (type-alst (type-to-types-alist-fix type-alst))
         (closure (symbol-list-fix closure))
         (clock (nfix clock))
         ((if (zp clock)) closure)
         (exist? (member-equal type closure))
         ((if exist?) closure)
         (new-closure (cons type closure))
         (item (assoc-equal type type-alst))
         ((unless item)
          (er hard? 'type-inference-bottomup=>super/subtype
              "Type ~p0 doesn't exist in the supertype alist.~%" type))
         ((unless (cdr item)) new-closure)
         (type-lst (cdr item)))
      (super/subtype-list type-lst type-alst new-closure (1- clock))))

  (define super/subtype-list ((type-lst symbol-listp)
                              (type-alst type-to-types-alist-p)
                              (closure symbol-listp)
                              (clock natp))
    :measure (list (nfix clock) (acl2-count (symbol-list-fix type-lst)))
    :returns (closure symbol-listp)
    (b* ((type-lst (symbol-list-fix type-lst))
         (type-alst (type-to-types-alist-fix type-alst))
         (closure (symbol-list-fix closure))
         (clock (nfix clock))
         ((unless (consp type-lst)) closure)
         ((cons type-hd type-tl) type-lst)
         (new-closure (super/subtype type-hd type-alst closure clock)))
      (super/subtype-list type-tl type-alst new-closure clock)))
  )

(verify-guards super/subtype)

#|
(super/subtype 'integerp '((integerp . (rationalp maybe-integerp))
                           (maybe-integerp . (maybe-rationalp))
                           (rationalp . (maybe-rationalp))
                           (maybe-rationalp . nil))
               nil 4)

(super/subtype 'rationalp '((integerp . (rationalp maybe-integerp))
                           (maybe-integerp . (maybe-rationalp))
                           (rationalp . (maybe-rationalp))
                           (maybe-rationalp . nil))
               nil 4)
|#

(local
 (defthm pseudo-termp-of-cadr-of-consp
   (implies (and (pseudo-termp x)
                 (not (equal (car x) 'quote))
                 (consp x)
                 (consp (cdr x)))
            (pseudo-termp (cadr x)))
   :hints (("Goal" :in-theory (enable pseudo-termp)))))

(define look-up-type-tuple-to-thm-alist ((root-type symbolp)
                                         (type symbolp)
                                         (thms type-tuple-to-thm-alist-p)
                                         (term pseudo-termp)
                                         (path-cond pseudo-termp)
                                         state)
  :returns (ok booleanp)
  :guard-hints (("Goal"
                 :in-theory (disable assoc-equal
                                     symbol-listp
                                     pseudo-term-listp-of-cdr-of-pseudo-termp
                                     default-cdr
                                     consp-of-pseudo-lambdap)))
  :ignore-ok t
  (b* ((thms (type-tuple-to-thm-alist-fix thms))
       (path-cond (pseudo-term-fix path-cond))
       (term (pseudo-term-fix term))
       (tuple (make-type-tuple :type root-type
                               :neighbour-type type))
       (conspair (assoc-equal tuple thms))
       ((unless conspair) nil)
       (thm-name (cdr conspair))
       (type-thm
        (acl2::meta-extract-formula-w thm-name (w state)))
       ((unless (pseudo-termp type-thm))
        (er hard? 'type-inference-bottomup=>look-up-type-tuple-to-thm-alist
            "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
            thm-name type-thm))
       (ok (case-match type-thm
             (('implies (!root-type var) (!type var)) t)
             (('implies type-predicates (!type var))
              (b* (((if (equal type 'quote)) nil)
                   (substed (term-substitution type-predicates var term t)))
                (path-test-list `(if (,root-type ,term) ,path-cond 'nil)
                                substed state)))
             (& nil))))
    ok))

(encapsulate ()
  (local (in-theory (disable (:definition pseudo-termp)
                             (:rewrite lambda-of-pseudo-lambdap))))
  (local
   (defthm assoc-equal-of-type-tuple-to-thm-alist-p
     (implies (and (type-tuple-to-thm-alist-p x)
                   (assoc-equal y x))
              (and (consp (assoc-equal y x))
                   (symbolp (cdr (assoc-equal y x)))))))

(define super/subtype-to-judgements ((root-type symbolp)
                                     (types symbol-listp)
                                     (term pseudo-termp)
                                     (thms type-tuple-to-thm-alist-p)
                                     (path-cond pseudo-termp)
                                     (acc pseudo-termp)
                                     state)
  :returns (judgements pseudo-termp)
  :measure (len types)
  (b* ((root-type (symbol-fix root-type))
       (types (symbol-list-fix types))
       (term (pseudo-term-fix term))
       (thms (type-tuple-to-thm-alist-fix thms))
       (acc (pseudo-term-fix acc))
       ((unless (consp types)) acc)
       ((cons types-hd types-tl) types)
       ((if (equal root-type types-hd))
        (super/subtype-to-judgements root-type types-tl term thms path-cond acc
                                     state))
       ((unless (look-up-type-tuple-to-thm-alist root-type types-hd thms
                                                 term path-cond state))
        acc)
       (type-term `(,types-hd ,term))
       ((if (path-test acc type-term state))
        (super/subtype-to-judgements root-type types-tl term thms path-cond acc
                                     state)))
    (super/subtype-to-judgements root-type types-tl term thms path-cond
                                 `(if ,type-term ,acc 'nil) state)))
)

(define super/subtype-judgement-single ((type-judgement pseudo-termp)
                                        (path-cond pseudo-termp)
                                        (type-alst type-to-types-alist-p)
                                        (thms type-tuple-to-thm-alist-p)
                                        (acc pseudo-termp)
                                        state)
  :guard (type-predicate-p type-judgement type-alst)
  :returns (judgements pseudo-termp)
  (b* ((type-judgement (pseudo-term-fix type-judgement))
       (type-alst (type-to-types-alist-fix type-alst))
       (acc (pseudo-term-fix acc))
       ((unless (mbt (type-predicate-p type-judgement type-alst))) acc)
       ((list root-type term) type-judgement)
       (clock (len type-alst))
       (super/subtypes
        (super/subtype root-type type-alst nil clock)))
    (super/subtype-to-judgements root-type super/subtypes term thms path-cond
                                 acc state)))

(define super/subtype-judgements-acc ((judge pseudo-termp)
                                      (path-cond pseudo-termp)
                                      (type-alst type-to-types-alist-p)
                                      (thms type-tuple-to-thm-alist-p)
                                      (acc pseudo-termp)
                                      state)
  :returns (judgements pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judge))
  :verify-guards nil
  (b* ((judge (pseudo-term-fix judge))
       (acc (pseudo-term-fix acc))
       ((if (type-predicate-p judge type-alst))
        (super/subtype-judgement-single judge path-cond type-alst thms acc state))
       ((unless (is-conjunct? judge)) acc)
       ((if (equal judge ''t)) acc)
       ((list* & cond then &) judge)
       (first-acc (super/subtype-judgements-acc cond path-cond type-alst thms
                                                acc state)))
    (super/subtype-judgements-acc then path-cond type-alst thms first-acc
                                  state)))

(verify-guards super/subtype-judgements-acc)

(define super/subtype-judgements-fn ((judge pseudo-termp)
                                     (path-cond pseudo-termp)
                                     (type-alst type-to-types-alist-p)
                                     (thms type-tuple-to-thm-alist-p)
                                     state)
  :returns (judgements pseudo-termp)
  (super/subtype-judgements-acc judge path-cond type-alst thms judge state))

#|
(defthm test (implies (integerp x) (rationalp x)))
(defoption maybe-integerp integerp :pred maybe-integerp)
(defthm test1 (implies (integerp x) (maybe-integerp x)))
(super/subtype-judgements-fn '(if (integerp x) 't 'nil) ''t
                             '((integerp . (rationalp maybe-integerp))
                               (rationalp . nil)
                               (maybe-integerp . nil))
                             '((((type . integerp) (neighbour-type . rationalp)) .
                                test)
                               (((type . integerp) (neighbour-type . maybe-integerp)) .
                                test1))
                             state)
|#

(defmacro super/subtype-judgements (judgements path-cond options state
                                               &key which)
  `(if (equal ,which :super)
       (super/subtype-judgements-fn ,judgements ,path-cond
                                    (type-options->supertype ,options)
                                    (type-options->supertype-thm ,options)
                                    ,state)
     (super/subtype-judgements-fn ,judgements ,path-cond
                                  (type-options->subtype ,options)
                                  (type-options->subtype-thm ,options)
                                  ,state)))

#|
(defthm test (implies (integerp x) (rationalp x)))
(super/subtype-judgements '(if (integerp x) 't 'nil) ''t
                          '((supertype (integerp rationalp)
                                       (rationalp))
                            (supertype-thm (((type . integerp)
                                             (neighbour-type . rationalp))
                                            . test))
                            (subtype)
                            (subtype-thm)
                            (functions)
                            (consp)
                            (basic)
                            (list)
                            (alist)
                            (prod)
                            (option)
                            (sum)
                            (abstract))
                          state
                          :which :super)
|#

;; extend-judgements first calcualte the subtypes then it calculate the
;; supertypes based on the subtypes
(define extend-judgements ((judgements pseudo-termp)
                           (path-cond pseudo-termp)
                           (options type-options-p)
                           state)
  :returns (new-judgements pseudo-termp)
  (super/subtype-judgements
   (super/subtype-judgements judgements path-cond options state :which :sub)
   path-cond options state :which :super))

;; reduce not's in term
(define simple-transformer ((term pseudo-termp))
  :returns (new-term pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (new-term
        (case-match term
          (('not ('not term1)) term1)
          (& term))))
    new-term))

;;-------------------------------------------------------
;; Returns judgmenets

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
        (er hard? 'type-inference-bottomup=>construct-returns-judgement
            "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
            returns-name returns-thm))
       ((mv ok type)
        (case-match returns-thm
          ((!return-type (!fn . &))  (mv t return-type))
          ((('lambda r (!return-type r)) (!fn . &)) (mv t return-type))
          (('implies type-predicates (!return-type (!fn . formals)))
           (b* (((unless (symbol-listp formals)) (mv nil nil))
                (substed (term-substitution-multi type-predicates formals
                                                  actuals t))
                (yes? (path-test-list actuals-judgements substed state))
                ((if yes?) (mv t return-type)))
             (mv nil nil)))
          (& (mv nil nil))))
       ((unless ok)
        (er hard? 'type-inference-bottomup=>construct-returns-judgement
            "The returns theorem for function ~p0 is of the wrong syntactic ~
               form ~p1~%" fn returns-thm)))
    `(,return-type (,fn ,@actuals))))
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
                                      (acc pseudo-termp)
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
       (acc (pseudo-term-fix acc))
       ((unless (is-conjunct? actuals-judgements))
        (er hard? 'type-inference-bottomup=>returns-judgement-single-arg
            "Actuals judgements is not a conjunct ~p0.~%" actuals-judgements))
       (arg-check (arg-check-fix arg-check))
       ((unless (consp arg-check)) acc)
       ((cons check-hd check-tl) arg-check)
       ((cons type arg-decl) check-hd)
       ((unless (mbt (and (consp actuals)
                          (not (equal actuals-judgements ''t)))))
        nil)
       ((cons actual actuals-tl) actuals)
       ((list & actual-judge actuals-judge-tl &) actuals-judgements)
       ((if (equal type 't))
        (returns-judgement fn actuals-tl actuals-total
                           actuals-judge-tl actuals-judgements-total arg-decl
                           acc state))
       (guard-term `(,type ,actual))
       (yes? (path-test actual-judge guard-term state))
       ((unless yes?)
        (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
                                      actuals-judgements-total check-tl acc state))
       (new-acc
        (returns-judgement fn actuals-tl actuals-total
                           actuals-judge-tl actuals-judgements-total arg-decl
                           acc state)))
    (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
                                  actuals-judgements-total check-tl new-acc state)))

(define returns-judgement ((fn symbolp)
                           (actuals pseudo-term-listp)
                           (actuals-total pseudo-term-listp)
                           (actuals-judgements pseudo-termp)
                           (actuals-judgements-total pseudo-termp)
                           (arg-decl arg-decl-p)
                           (acc pseudo-termp)
                           state)
  :returns (judgements pseudo-termp)
  :measure (list (len (pseudo-term-list-fix actuals))
                 (acl2-count (arg-decl-fix arg-decl)))
  :guard (not (equal fn 'quote))
  (b* (((unless (mbt (not (equal fn 'quote)))) nil)
       (actuals (pseudo-term-list-fix actuals))
       (actuals-judgements (pseudo-term-fix actuals-judgements))
       (arg-decl (arg-decl-fix arg-decl))
       (acc (pseudo-term-fix acc))
       ((if (and (equal (arg-decl-kind arg-decl) :done)
                 (null actuals)
                 (equal actuals-judgements ''t)))
        (progn$ (cw "fn: ~p0, actuals: ~p1~%" fn actuals-total)
                (cw "actuals-judgements-total: ~p0~%" actuals-judgements-total)
        `(if ,(construct-returns-judgement fn actuals-total
                                           actuals-judgements-total
                                           (arg-decl-done->r arg-decl)
                                           state)
             ,acc 'nil)))
       ((if (and (equal (arg-decl-kind arg-decl) :done)
                 (or actuals (not (equal actuals-judgements ''t)))))
        (er hard? 'type-inference-bottomup=>returns-judgement
            "Run out of arg-decls.~%"))
       ((if (or (null actuals)
                (equal actuals-judgements ''t)))
        (er hard? 'type-inference-bottomup=>returns-judgement
            "Run out of actuals or actuals-judgements.~%"))
       (arg-check (arg-decl-next->next arg-decl)))
    (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
                                  actuals-judgements-total arg-check acc state)))
)

(verify-guards returns-judgement
  :hints (("Goal"
           :in-theory (disable pseudo-termp))))

;;-------------------------------------------------------
;; quoted judgements

(encapsulate ()
  (local (in-theory (disable (:definition pseudo-termp)
                             (:definition assoc-equal)
                             (:definition symbol-listp)
                             (:rewrite lambda-of-pseudo-lambdap))))

(define type-judgement-nil-list ((list list-type-description-alist-p)
                                 (acc pseudo-termp)
                                 state)
  :returns (judgements pseudo-termp)
  :measure (len (list-type-description-alist-fix list))
  (b* ((list (list-type-description-alist-fix list))
       (acc (pseudo-term-fix acc))
       ((unless (consp list)) acc)
       ((cons list-hd list-tl) list)
       ((cons type &) list-hd)
       ((mv & yes?) (acl2::magic-ev-fncall type '(nil) state t nil))
       ((unless yes?)
        (er hard? 'type-inference-bottomup=>type-judgement-nil-list
            "list type ~p0 failed the nil check.~%" type))
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
       ((cons type &) alist-hd)
       ((mv & yes?) (acl2::magic-ev-fncall type '(nil) state t nil))
       ((unless yes?)
        (er hard? 'type-inference-bottomup=>type-judgement-nil-alist
            "alist type ~p0 failed the nil check.~%" type))
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
       ((cons type &) option-hd)
       ((mv & yes?) (acl2::magic-ev-fncall type '(nil) state t nil))
       ((unless yes?)
        (er hard? 'type-inference-bottomup=>type-judgement-option
            "option type ~p0 failed the nil check.~%" type))
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
       (const (cadr term)))
    (cond ((integerp const)
           (extend-judgements `(if (integerp ',const) 't 'nil) ''t options state))
          ((rationalp const)
           (extend-judgements `(if (rationalp ',const) 't 'nil) ''t options state))
          ((equal const t)
           (extend-judgements (type-judgement-t) ''t options state))
          ((null const) (type-judgement-nil options state))
          ((symbolp const)
           (extend-judgements `(if (symbolp ',const) 't 'nil) ''t options state))
          (t (er hard? 'type-inference-bottomup=>type-judgement-quoted
                 "Type inference for constant term ~p0 is not supported.~%"
                 term)))))

;; ------------------------------------------------------------------
;;    Variable judgements

(define type-judgement-variable ((term pseudo-termp)
                                 (path-cond pseudo-termp)
                                 (options type-options-p)
                                 state)
  :returns (judgements pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (path-cond (pseudo-term-fix path-cond))
       (options (type-options-fix options))
       (supertype (type-options->supertype options))
       (judge-from-path-cond (look-up-path-cond term path-cond supertype)))
    (extend-judgements judge-from-path-cond path-cond options state)))

;; ------------------------------------------------------------------
;;    The main type-judgements

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
         (actuals-judgements
          (type-judgement-list actuals path-cond options state))
         (substed-actuals-judgements
          (term-substitution-multi actuals-judgements actuals formals t))
         (body-judgements
          (type-judgement body `(if ,shadowed-path-cond
                                    ,substed-actuals-judgements 'nil)
                          options state))
         (lambda-judgements
          `((lambda ,formals
              (if ,body-judgements
                  ,substed-actuals-judgements
                'nil))
            ,@actuals))
         (return-judgement
          (term-substitution (type-judgement-top body-judgements body options)
                             body term t)))
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
          (er hard? 'type-inference-bottomup=>type-judgement-if
              "Mangled if term: ~q0" term))
         ((list cond then else) actuals)
         (judge-cond (type-judgement cond path-cond options state))
         (judge-then
          (type-judgement then `(if ,(simple-transformer cond) ,path-cond 'nil)
                          options state))
         (judge-else
          (type-judgement else
                          `(if ,(simple-transformer `(not ,cond)) ,path-cond 'nil)
                          options state))
         (judge-then-top (type-judgement-top judge-then then options))
         (judge-else-top (type-judgement-top judge-else else options))
         (judge-from-then (term-substitution judge-then-top then term t))
         (judge-from-else (term-substitution judge-else-top else term t))
         (judge-if-top (union-judgements judge-from-then judge-from-else state))
         (judge-if-top-extended
          (extend-judgements judge-if-top path-cond options state)))
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
         (actuals-judgements
          (type-judgement-list actuals path-cond options state))
         (actuals-judgements-top
          (type-judgement-top-list actuals-judgements actuals options))
         (functions (type-options->functions options))
         (conspair (assoc-equal fn functions))
         ((unless conspair)
          (er hard? 'type-inference-bottomup=>type-judgement-fn
              "There exists no function description for function ~p0. ~%" fn))
         (fn-description (cdr conspair))
         ;; return-judgement could be ''t which means it could be anything
         (return-judgement
          (returns-judgement fn actuals actuals actuals-judgements-top
                             actuals-judgements-top fn-description ''t state))
         ((if (equal return-judgement ''t))
          (er hard? 'type-inference-bottomup=>type-judgement-fn
              "Failed to find type judgements for return of function call ~
               ~p0~%" term))
         (return-judgement-extended
          (extend-judgements return-judgement path-cond options state)))
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
          (type-judgement-variable term path-cond options state))
         ((if (acl2::quotep term))
          (type-judgement-quoted term options state))
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
