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
(include-book "typed-term")
(include-book "judgement-fns")

(set-state-ok t)

(define term-substitution-conj ((term pseudo-termp)
                                (subterm-lst pseudo-term-listp)
                                (subst-lst pseudo-term-listp)
                                (skip-conj booleanp))
  :returns (substed pseudo-termp)
  :measure (acl2-count (pseudo-term-fix term))
  (b* ((term (pseudo-term-fix term))
       (subterm-lst (pseudo-term-list-fix subterm-lst))
       (subst-lst (pseudo-term-list-fix subst-lst))
       ((if (equal term ''t)) ''t)
       ((unless (and (consp subterm-lst)
                     (consp subst-lst)))
        (er hard? 'type-inference-bottomup=>term-substitution-conj
            "Subterm-lst or subst-lst is empty.~%"))
       ((cons subterm-hd subterm-tl) subterm-lst)
       ((cons subst-hd subst-tl) subst-lst)
       ((unless (is-conjunct? term))
        (term-substitution term subterm-hd subst-hd skip-conj))
       ((list & first rest &) term))
    `(if ,(term-substitution first subterm-hd subst-hd skip-conj)
         ,(term-substitution-conj rest subterm-tl subst-tl skip-conj)
       'nil)))

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
                                     (path-cond pseudo-termp)
                                     (supertype type-to-types-alist-p)
                                     state)
  :returns (judgement pseudo-termp)
  :guard (not (equal fn 'quote))
  :ignore-ok t
  (b* ((fn (symbol-fix fn))
       ((unless (mbt (not (equal fn 'quote)))) nil)
       (actuals (pseudo-term-list-fix actuals))
       (return-spec (return-spec-fix return-spec))
       (formals (return-spec->formals return-spec))
       (returns-name (return-spec->returns-thm return-spec))
       (return-type (return-spec->return-type return-spec))
       (returns-thm
        (acl2::meta-extract-formula-w returns-name (w state)))
       ((unless (pseudo-termp returns-thm))
        (er hard? 'type-inference-bottomup=>construct-returns-judgement
            "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
            returns-name returns-thm))
       ((mv ok return-judge)
        (case-match returns-thm
          ((!return-type (!fn . &))
           (mv t `(,return-type (,fn ,@actuals))))
          ((('lambda r conclusions) (!fn . &))
           (b* (((unless (symbol-listp formals)) (mv nil nil))
                (substed-conclusions
                 (term-substitution conclusions `(,fn ,@formals)
                                    `(,fn ,@actuals) t))
                (return-judge
                 (look-up-path-cond `(,fn ,@actuals) substed-conclusions supertype)))
             (mv t return-judge)))
          (('implies type-predicates conclusions)
           (b* (((unless (symbol-listp formals)) (mv nil nil))
                (substed
                 (term-substitution-conj type-predicates formals actuals t))
                (yes?
                 (path-test-list `(if ,path-cond ,actuals-judgements 'nil)
                                 substed state))
                ((unless yes?) (mv nil nil))
                (substed-conclusions
                 (term-substitution conclusions `(,fn ,@formals)
                                    `(,fn ,@actuals) t))
                (return-judge
                 (look-up-path-cond `(,fn ,@actuals) substed-conclusions supertype)))
             (mv t return-judge)))
          (& (b* (((unless (symbol-listp formals)) (mv nil nil))
                  (substed-conclusions
                   (term-substitution returns-thm `(,fn ,@formals)
                                      `(,fn ,@actuals) t))
                  (return-judge
                   (look-up-path-cond `(,fn ,@actuals) substed-conclusions supertype)))
               (mv t return-judge)))))
       ((unless ok)
        (er hard? 'type-inference-bottomup=>construct-returns-judgement
            "The returns theorem for function ~p0 is of the wrong syntactic ~
               form ~p1~%" fn returns-thm)))
    return-judge))
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
                                      (path-cond pseudo-termp)
                                      (supertype type-to-types-alist-p)
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
                           path-cond supertype acc state))
       (guard-term `(,type ,actual))
       (yes? (path-test actual-judge guard-term state))
       ((unless yes?)
        (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
                                      actuals-judgements-total check-tl
                                      path-cond supertype acc state))
       (new-acc
        (returns-judgement fn actuals-tl actuals-total
                           actuals-judge-tl actuals-judgements-total arg-decl
                           path-cond supertype acc state)))
    (returns-judgement-single-arg fn actuals actuals-total actuals-judgements
                                  actuals-judgements-total check-tl path-cond
                                  supertype new-acc state)))

(define returns-judgement ((fn symbolp)
                           (actuals pseudo-term-listp)
                           (actuals-total pseudo-term-listp)
                           (actuals-judgements pseudo-termp)
                           (actuals-judgements-total pseudo-termp)
                           (arg-decl arg-decl-p)
                           (path-cond pseudo-termp)
                           (supertype type-to-types-alist-p)
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
        `(if ,(construct-returns-judgement fn actuals-total
                                           actuals-judgements-total
                                           (arg-decl-done->r arg-decl)
                                           path-cond supertype state)
             ,acc 'nil))
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
                                  actuals-judgements-total arg-check path-cond
                                  supertype acc state)))
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
                 (equal (len formals) (len actuals)))
            (pseudo-termp `((lambda ,formals
                              ,body-judgements)
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
          (term-substitution-conj actuals-judgements actuals formals t))
         (body-judgements
          (type-judgement body `(if ,shadowed-path-cond
                                    ,substed-actuals-judgements 'nil)
                          options state))
         (lambda-judgements
          `((lambda ,formals
              ,body-judgements)
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
         (judge-if-top (union-judgements judge-from-then judge-from-else
                                         state))
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
                             actuals-judgements-top fn-description path-cond
                             (type-options->supertype options) ''t state))
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
