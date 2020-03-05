;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (Feb 13th 2020)
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
(include-book "clause-processors/generalize" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "basics")
;; (include-book "alist")
(include-book "hint-please")
(include-book "typed-term")
(include-book "judgement-fns")
(include-book "type-options")

(set-state-ok t)

;; This clause-processor projections a term that uses alists into a term that
;; uses arrays. Supposedly other isomorphic projectionations can also be made in
;; a similar way.

(define new-fresh-vars ((n natp)
                        (current symbol-listp))
  :returns (new-vars symbol-listp
                     :hints (("Goal" :in-theory (enable
                                                 acl2::new-symbols-from-base))))
  (acl2::new-symbols-from-base n 'x current)
  ///
  (more-returns
   (new-vars (implies (and (natp n)
                           (symbol-listp current))
                      (equal (len new-vars) n))
             :name len-of-new-fresh-vars)))

(define new-fresh-var ((current symbol-listp))
  :returns (new-var symbolp)
  (car (new-fresh-vars 1 current)))

;; ---------------------------------------------------------------
(encapsulate ()
  (local (in-theory (disable symbol-listp
                             acl2::pseudo-termp-opener
                             pseudo-term-listp-of-symbol-listp
                             consp-of-pseudo-lambdap
                             rational-listp
                             integer-listp)))

  ;; find the alist-array-equiv of term from projection
  ;; projection should be a conjunction of equivalence terms
  (define find-projection ((term pseudo-termp) (projection pseudo-termp))
    :returns (the-proj pseudo-termp)
    :measure (acl2-count (pseudo-term-fix projection))
    (b* ((term (pseudo-term-fix term))
         (projection (pseudo-term-fix projection))
         ((mv ok proj)
          (case-match projection
            (('alist-array-equiv !term &) (mv t projection))
            (& (mv nil nil))))
         ((if ok) proj)
         ((unless (is-conjunct? projection))
          (er hard? 'term-projection=>find-projection
              "Projection is not a conjunction: ~q0" projection))
         ((if (equal projection ''t)) nil)
         ((list & proj-hd proj-tl &) projection)
         (hd-res (find-projection term proj-hd))
         ((if hd-res) hd-res))
      (find-projection term proj-tl)))
  )

;; ---------------------------------------------------------------

(encapsulate ()
  (local
   (in-theory (disable assoc-equal symbol-listp lambda-of-pseudo-lambdap
                       consp-of-pseudo-lambdap
                       pseudo-lambdap-of-fn-call-of-pseudo-termp
                       consp-of-is-conjunct? default-cdr
                       acl2::true-listp-of-car-when-true-list-listp
                       true-list-listp true-listp)))

  ;; example: alist-term = (integer-integer-alistp x)
  ;; fresh-var = y
  ;; 1. Generate constraint: y = (alist-to-array-fn x)
  ;; 2. Use the theorem to establish (alist-array-equiv x y):
  ;; thm: (implies (and (integer-integer-alistp a)
  ;;                    (equal b (integer-integer-alist-to-array a)))
  ;;               (alist-array-equiv a b))
  (define new-projection ((alist-term pseudo-termp)
                          (fresh-var symbolp)
                          (options type-options-p)
                          state)
    :returns (new-proj pseudo-termp)
    :guard (and (consp alist-term)
                (symbolp (car alist-term))
                (not (equal (car alist-term) 'quote))
                (not (null (is-alist? (car alist-term) options))))
    (b* (((unless (mbt (and (pseudo-termp alist-term)
                            (symbolp fresh-var)
                            (type-options-p options)
                            (consp alist-term)
                            (symbolp (car alist-term))
                            (not (equal (car alist-term) 'quote))
                            (not (null (is-alist? (car alist-term) options))))))
          nil)
         ((type-options to) options)
         ((cons fn actuals) alist-term)
         (var (car actuals))
         (yes? (assoc-equal fn to.alist))
         ((unless yes?)
          (er hard? 'term-projection=>new-projection
              "An alist-info item is required for alist type: ~q0" fn))
         ((a2a-info a) (cdr yes?))
         (new-constraint `(alist-array-equiv ,fresh-var (,a.a2a-fn ,var)))
         (equiv-thm
          (acl2::meta-extract-formula-w a.thm (w state)))
         ((unless (pseudo-termp equiv-thm))
          (er hard? 'term-projection=>new-projection
              "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
              a.thm equiv-thm))
         ((mv ok proj)
          (case-match equiv-thm
            (('implies hypo ('alist-array-equiv !a.formals))
             (b* ((substed-hypo
                   (term-substitution hypo
                                      (pairlis$ a.formals
                                                `(,var ,fresh-var))
                                      t))
                  (yes? (path-test-list `(if ,alist-term ,new-constraint 'nil)
                                        substed-hypo state))
                  ((unless yes?) (mv nil nil)))
               (mv t `(alist-array-equiv ,var ,fresh-var))))
            (& (mv nil nil))))
         ((unless ok)
          (er hard? 'term-projection=>new-projection
              "Can't match the theorem: ~q0" equiv-thm)))
      proj))
  )

(encapsulate ()
  (local (in-theory (disable pseudo-termp consp-of-is-conjunct?
                             symbol-listp
                             equal-fixed-and-x-of-pseudo-termp
                             pseudo-term-listp-of-symbol-listp
                             lambda-of-pseudo-lambdap
                             acl2::symbol-listp-of-cdr-when-symbol-listp
                             acl2::pseudo-termp-cadr-from-pseudo-term-listp
                             acl2::symbol-listp-when-not-consp
                             pseudo-lambdap-of-fn-call-of-pseudo-termp)))

  (define generate-fncall-proj-cases ((fn symbolp)
                                      (tta typed-term-list-p)
                                      (ntta typed-term-list-p)
                                      (actuals-proj pseudo-termp)
                                      (hypo pseudo-termp)
                                      (concl pseudo-termp)
                                      (options type-options-p)
                                      state)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt options)))
                 (new-proj pseudo-termp))
    :guard (and (not (equal fn 'quote))
                (good-typed-term-list-p tta options)
                (good-typed-term-list-p ntta options))
    :verify-guards nil
    (b* (((unless (mbt (and (symbolp fn)
                            (not (equal fn 'quote))
                            (typed-term-list-p tta)
                            (good-typed-term-list-p tta options)
                            (typed-term-list-p ntta)
                            (good-typed-term-list-p ntta options)
                            (pseudo-termp actuals-proj)
                            (pseudo-termp hypo)
                            (pseudo-termp concl)
                            (type-options-p options))))
          (mv (make-typed-term) nil))
         (tta.term-lst (typed-term-list->term-lst tta))
         (tta.judgements (typed-term-list->judgements tta))
         (ntta.judgements (typed-term-list->judgements ntta))
         (ntta.path-cond (typed-term-list->path-cond ntta))
         ((type-options to) options)
         (all-known `(if ,tta.judgements
                         (if ,ntta.judgements
                             ,actuals-proj
                           'nil)
                       'nil))
         (yes? (path-test-list all-known hypo state))
         ((unless yes?)
          (prog2$ (er hard? 'term-projection=>generate-fncall-proj-cases
                      "Can't discharge the hypotheses: ~q0" hypo)
                  (mv (make-typed-term) nil)))
         (term `(,fn ,@tta.term-lst))
         (new-proj (find-projection term concl))
         ((mv ok new-term new-judge)
          (case-match new-proj
            (('alist-array-equiv !term new-term)
             (b* (((mv ok new-judge)
                   (case-match new-term
                     ((store-fn k (cons-fn k v) ar)
                      (b* (((unless (and (symbolp store-fn)
                                         (symbolp cons-fn)
                                         (not (equal store-fn 'quote))
                                         (not (equal cons-fn 'quote))))
                            (mv nil nil))
                           (cons-term `(,cons-fn ,k ,v))
                           (store-term `(,store-fn ,k (,cons-fn ,k ,v) ,ar))
                           (judge-k (look-up-path-cond ntta.judgements k to.supertype))
                           (judge-v (look-up-path-cond ntta.judgements v to.supertype))
                           (judge-ar
                            (look-up-path-cond ntta.judgements ar to.supertype))
                           (judge-cons-fn
                            (look-up-path-cond cons-term concl to.supertype))
                           (judge-cons-full `(if ,judge-cons-fn
                                                 (if ,judge-k
                                                     (if ,judge-v
                                                         't
                                                       'nil))))
                           (judge-store-fn
                            (look-up-path-cond store-term concl to.supertype)))
                        (mv t `(if ,judge-store-fn
                                   (if ,judge-k
                                       (if ,judge-cons-full
                                           (if ,judge-ar
                                               't
                                             'nil)
                                         'nil)
                                     'nil)
                                 'nil))))
                     ;; other cases need to be implemented
                     (& (mv nil nil)))))
               (mv ok new-term new-judge)))
            (& (mv nil nil nil))))
         ((unless ok)
          (prog2$
           (er hard? 'term-projection=>generate-fncall-proj-cases
               "Malformed hypotheses and conclusion: ~p0 and ~p1~%"
               hypo concl)
           (mv (make-typed-term) nil))))
      (mv (make-typed-term
           :term new-term
           :path-cond ntta.path-cond
           :judgements new-judge)
          new-proj)))
  )

(verify-guards generate-fncall-proj-cases
  :hints (("Goal"
           :in-theory (disable consp-of-is-conjunct? pseudo-term-listp
                               symbol-listp acl2::pseudo-termp-opener
                               pseudo-term-listp-of-symbol-listp
                               member-equal true-list-listp
                               acl2::symbolp-of-car-when-symbol-listp
                               acl2::true-listp-of-car-when-true-list-listp
                               pseudo-term-listp-of-cdr-of-pseudo-termp))))

(encapsulate ()
  (local (in-theory (disable pseudo-termp assoc-equal
                             consp-of-pseudo-lambdap
                             pseudo-lambdap-of-fn-call-of-pseudo-termp
                             symbol-listp)))

  (local
   (defthm append-of-pseudo-term-listp
     (implies (and (pseudo-term-listp x)
                   (pseudo-term-listp y))
              (pseudo-term-listp (append x y)))))

  (local
   (defthm append-of-symbol-listp
     (implies (and (symbol-listp x)
                   (symbol-listp y))
              (symbol-listp (append x y)))))

  (local
   (defthm pseudo-term-alist-of-pairlis$
     (implies (and (pseudo-term-listp x)
                   (symbol-listp y))
              (pseudo-term-alistp (pairlis$ x y)))))

  (define generate-fncall-proj ((fn symbolp)
                                (actuals-tterm typed-term-list-p)
                                (new-actuals-tterm typed-term-list-p)
                                (actuals-proj pseudo-termp)
                                (options type-options-p)
                                state)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt options)))
                 (new-proj pseudo-termp))
    :guard (and (not (equal fn 'quote))
                (good-typed-term-list-p actuals-tterm options)
                (good-typed-term-list-p new-actuals-tterm options))
    (b* (((unless (mbt (and (symbolp fn)
                            (not (equal fn 'quote))
                            (typed-term-list-p actuals-tterm)
                            (good-typed-term-list-p actuals-tterm options)
                            (typed-term-list-p new-actuals-tterm)
                            (good-typed-term-list-p new-actuals-tterm options)
                            (pseudo-termp actuals-proj)
                            (type-options-p options))))
          (mv (make-typed-term) nil))
         ((typed-term-list att) actuals-tterm)
         ((typed-term-list natt) new-actuals-tterm)
         ((type-options to) options)
         (exist? (assoc-equal fn to.aa-map))
         ((unless exist?)
          (prog2$ (er hard? 'term-projection=>generate-fncall-proj
                      "There isn't an alist-array-map item for function ~p0.~%" fn)
                  (mv (make-typed-term) nil)))
         ((equiv eq) (cdr exist?))
         (equiv-thm (acl2::meta-extract-formula-w eq.thm (w state)))
         ((unless (pseudo-termp equiv-thm))
          (prog2$ (er hard? 'term-projection=>generate-fncall-proj
                      "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
                      eq.thm equiv-thm)
                  (mv (make-typed-term) nil)))
         (fn-formals (strip-cars eq.formal-map))
         (fn-equiv-formals (strip-cdrs eq.formal-map))
         (both-actuals (append att.term-lst natt.term-lst))
         (both-formals (append fn-formals fn-equiv-formals))
         (substed-thm
          (term-substitution equiv-thm (pairlis$ both-actuals both-formals) t))
         ((mv ok new-tt new-proj)
          (case-match substed-thm
            (('implies hypo concl)
             (b* (((mv new-tt new-proj)
                   (generate-fncall-proj-cases fn att natt actuals-proj hypo
                                               concl to state)))
               (mv t new-tt new-proj)))
            (& (mv nil (make-typed-term) nil))))
         ((unless ok)
          (prog2$ (er hard? 'term-projection=>generate-fncall-proj
                      "Equivalence theorem is malformed: ~q0" substed-thm)
                  (mv (make-typed-term) nil))))
      (mv new-tt new-proj)))
  )

(encapsulate ()
  (local (in-theory (disable symbol-listp
                             acl2::pseudo-termp-opener
                             pseudo-term-listp-of-symbol-listp
                             acl2::symbol-listp-when-not-consp
                             consp-of-is-conjunct?)))

  (define generate-if-proj ((term pseudo-termp)
                            (cond-tterm typed-term-p)
                            (then pseudo-termp)
                            (then-tterm typed-term-p)
                            (then-proj pseudo-termp)
                            (else pseudo-termp)
                            (else-tterm typed-term-p)
                            (else-proj pseudo-termp)
                            state)
    :returns (mv (new-t pseudo-termp)
                 (new-proj pseudo-termp))
    (b* ((term (pseudo-term-fix term))
         ((typed-term ctt) (typed-term-fix cond-tterm))
         (then (pseudo-term-fix then))
         ((typed-term ttt) (typed-term-fix then-tterm))
         (then-proj (pseudo-term-fix then-proj))
         (else (pseudo-term-fix else))
         ((typed-term ett) (typed-term-fix else-tterm))
         (else-proj (pseudo-term-fix else-proj))
         (new-term `(if ,ctt.term ,ttt.term ,ett.term)))
      (cond ((and (path-test then-proj `(alist-array-equiv ,then ,ttt.term) state)
                  (path-test else-proj `(alist-array-equiv ,else ,ett.term) state))
             (mv new-term `(alist-array-equiv ,term ,new-term)))
            (t (mv (er hard? 'term-projection=>generate-if-proj
                       "Inconsistent if projections.~%then: ~p0~% ~
                      else: ~p1~%" then-proj else-proj)
                   nil)))))
  )

(define generate-lambda-proj ((term pseudo-termp)
                              (new-formals symbol-listp)
                              (actuals-tterm typed-term-list-p)
                              (body pseudo-termp)
                              (body-tterm typed-term-p)
                              (body-proj pseudo-termp)
                              state)
  :returns (mv (new-term pseudo-termp)
               (new-proj pseudo-termp))
  :guard (equal (len new-formals)
                (len (typed-term-list->term-lst actuals-tterm)))
  (b* ((term (pseudo-term-fix term))
       (new-formals (symbol-list-fix new-formals))
       ((typed-term-list att) (typed-term-list-fix actuals-tterm))
       ((unless (mbt (equal (len new-formals) (len att.term-lst))))
        (mv nil nil))
       (body (pseudo-term-fix body))
       ((typed-term btt) (typed-term-fix body-tterm))
       (body-proj (pseudo-term-fix body-proj))
       (new-term `((lambda ,new-formals ,btt.term) ,@att.term-lst)))
    (cond ((path-test body-proj `(alist-array-equiv ,body ,btt.term) state)
           (mv new-term `(alist-array-equiv ,term ,new-term)))
          (t (mv (er hard? 'term-projection=>lambda-projection
                     "Inconsistent lambda projections.~%body projection: ~p0~%"
                     body-proj)
                 nil)))))

;; For a variable, if its judgement says it's an alist, the projection should
;; contain:
;;   (alist-array-equiv the-var new-var)
;; If so, generate new term using new-var, and new judgement by substituting in
;; the new term.
(define variable-projection ((tterm typed-term-p)
                             (path-cond pseudo-termp)
                             (projection pseudo-termp)
                             (names symbol-listp)
                             (options type-options-p))
  :returns (mv (new-tt (and (typed-term-p new-tt)
                            (good-typed-term-p new-tt options)))
               (new-proj pseudo-termp)
               (new-names symbol-listp))
  :guard (and (good-typed-term-p tterm options)
              (equal (typed-term->kind tterm) 'variablep))
  :guard-hints (("Goal" :in-theory (enable typed-term->kind)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (pseudo-termp path-cond)
                          (pseudo-termp projection)
                          (symbol-listp names)
                          (type-options-p options)
                          (good-typed-term-p tterm options)
                          (equal (typed-term->kind tterm) 'variablep))))
        (mv (make-typed-term)
            (pseudo-term-fix projection)
            (symbol-list-fix names)))
       ((typed-term tt) tterm)
       ((type-options to) options)
       (the-proj (find-projection tt.term projection))
       ((unless the-proj) (mv tt ''t names))
       ((mv err new-term)
        (case-match the-proj
          (('alist-array-equiv !tt.term new-term) (mv nil new-term))
          (& (mv t nil))))
       ((if err) (mv (make-typed-term) ''t names))
       ((unless (acl2::variablep new-term))
        (prog2$ (er hard? 'term-projection=>variable-projection
                    "Projecting a variable into a non-variable: ~p0 and ~p1~%"
                    tt.term new-term)
                (mv (make-typed-term) ''t names)))
       (judge (look-up-path-cond new-term path-cond to.supertype))
       (new-tt (make-typed-term :term new-term
                                :path-cond path-cond
                                :judgements judge)))
    (mv new-tt the-proj names)))

(local (in-theory (disable (:executable-counterpart typed-term)
                           (:executable-counterpart typed-term-list))))

(defines term-projection
  :well-founded-relation l<
  :verify-guards nil
  :returns-hints (("Goal"
                   :in-theory (disable consp-of-is-conjunct?
                                       pseudo-term-listp-of-symbol-listp)))

  (define lambda-projection ((tterm typed-term-p)
                             (path-cond pseudo-termp)
                             (projection pseudo-termp)
                             (names symbol-listp)
                             (options type-options-p)
                             state)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt options)))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'lambdap))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (type-options-p options)
                            (symbol-listp names)
                            (pseudo-termp projection)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'lambdap))))
          (mv (make-typed-term)
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((typed-term tt) tterm)
         (formals (lambda-formals (car tt.term)))
         ((typed-term-list tta) (typed-term-lambda->actuals tterm options))
         ((typed-term ttb) (typed-term-lambda->body tterm options))
         ((typed-term ttt) (typed-term->top tt options))
         ((mv ptta proja namesa)
          (term-list-projection tta path-cond projection names options state))
         ((typed-term-list ptta) ptta)
         (new-formals (new-fresh-vars (len formals) (append formals namesa)))
         (namesf (append new-formals namesa))
         (both-actuals (append tta.term-lst ptta))
         (both-formals (append formals new-formals))
         (shadowed-path-cond (shadow-path-cond new-formals path-cond))
         (substed-actuals-judgements
          (term-substitution ptta.judgements
                             (pairlis$ ptta.term-lst new-formals) t))
         (shadowed-proj (shadow-path-cond new-formals projection))
         (substed-proja
          (term-substitution proja (pairlis$ both-actuals both-formals) t))
         ((mv pttb projb namesb)
          (term-projection ttb
                           `(if ,shadowed-path-cond
                                ,substed-actuals-judgements 'nil)
                           `(if ,shadowed-proj ,substed-proja 'nil)
                           namesf options state))
         ((typed-term pttb) pttb)
         ((unless (mbt (equal (len new-formals) (len ptta))))
          (mv (make-typed-term) nil nil))
         ((mv new-term new-proj)
          (generate-lambda-proj tt.term new-formals ptta ttb.term pttb
                                projb state))
         (new-judge `((lambda ,new-formals
                        ,pttb.judgements)
                      ,@ptta.term-lst))
         (new-top (make-typed-term :term new-term
                                   :path-cond path-cond
                                   :judgements new-judge)))
      (mv (make-typed-lambda new-top pttb ptta options) new-proj namesb)))

  (define if-projection ((tterm typed-term-p)
                         (path-cond pseudo-termp)
                         (projection pseudo-termp)
                         (names symbol-listp)
                         (options type-options-p)
                         state)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt options)))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'ifp))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (type-options-p options)
                            (symbol-listp names)
                            (pseudo-termp projection)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'ifp))))
          (mv (make-typed-term)
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((typed-term tt) tterm)
         ((typed-term ttc) (typed-term-if->cond tt options))
         ((typed-term ttt) (typed-term-if->then tt options))
         ((typed-term tte) (typed-term-if->else tt options))
         ((typed-term tttop) (typed-term->top tt options))
         ((mv pttc projc namesc)
          (term-projection ttc path-cond projection names options state))
         ((mv pttt projt namest)
          (term-projection ttt
                           `(if ,(simple-transformer ttc.term)
                                ,path-cond 'nil)
                           `(if ,projc ,projection 'nil)
                           namesc options state))
         ((typed-term pttt) pttt)
         ((mv ptte proje namese)
          (term-projection tte
                           `(if ,(simple-transformer `(not ,ttc.term))
                                ,path-cond 'nil)
                           projection namest options state))
         ((typed-term ptte) ptte)
         ((mv new-term new-proj)
          (generate-if-proj tt.term pttc ttt.term pttt projt tte.term
                            ptte proje state))
         (new-judge (intersect-judgements pttt.judgements ptte.judgements state))
         (new-top (make-typed-term :term new-term
                                   :path-cond path-cond
                                   :judgements new-judge)))
      (mv (make-typed-if new-top pttc pttt ptte options)
          new-proj namese)))

  (define fncall-projection ((tterm typed-term-p)
                             (path-cond pseudo-termp)
                             (projection pseudo-termp)
                             (names symbol-listp)
                             (options type-options-p)
                             state)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt options)))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'fncallp))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (pseudo-termp projection)
                            (symbol-listp names)
                            (type-options-p options)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'fncallp))))
          (mv (make-typed-term)
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((type-options to) options)
         ((typed-term tt) tterm)
         ((typed-term-list tta) (typed-term-fncall->actuals tterm to))
         ((typed-term ttt) (typed-term->top tterm to))
         ((cons fn actuals) tt.term)
         ((mv ptta proja namesa)
          (term-list-projection tta path-cond projection names options state))
         ((if (is-alist? fn options))
          (b* (((unless (and (equal (len actuals) 1)
                             (symbolp (car actuals))))
                (prog2$
                 (er hard? 'term-projection=>fncall-projection
                     "We found a alist type recognizer, but its argument is not ~
                     a single variable: ~q0" tt.term)
                 (mv tt projection names)))
               (fresh-var (new-fresh-var namesa))
               (new-var-proj (new-projection tt.term fresh-var to.alist state))
               (new-names (cons fresh-var namesa))
               ((mv new-tt new-proj)
                (generate-fncall-proj fn tta ptta new-var-proj to state)))
            ;; adding array-p info into projection
            (mv new-tt new-proj new-names)))
         ((mv new-tt new-proj)
          (generate-fncall-proj fn tta ptta proja to.aa-map state)))
      (mv new-tt new-proj namesa)))

  (define term-projection ((tterm typed-term-p)
                           (path-cond pseudo-termp)
                           (projection pseudo-termp)
                           (names symbol-listp)
                           (options type-options-p)
                           state)
    :guard (good-typed-term-p tterm options)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt options)))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :measure (list (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (pseudo-termp projection)
                            (symbol-listp names)
                            (type-options-p options)
                            (good-typed-term-p tterm options))))
          (mv (make-typed-term) nil nil))
         ((typed-term tt) tterm)
         ((if (equal (typed-term->kind tterm) 'variablep))
          (variable-projection tterm path-cond projection names options))
         ((if (equal (typed-term->kind tterm) 'quotep))
          (mv tt `(alist-array-equiv ,tt.term ,tt.term) names))
         ((if (equal (typed-term->kind tterm) 'lambdap))
          (lambda-projection tterm path-cond projection names options state))
         ((if (equal (typed-term->kind tterm) 'ifp))
          (if-projection tterm path-cond projection names options state)))
      (fncall-projection tterm path-cond projection names options state)))

  (define term-list-projection ((tterm-lst typed-term-list-p)
                                (path-cond pseudo-termp)
                                (projection pseudo-termp)
                                (names symbol-listp)
                                (options type-options-p)
                                state)
    :guard (good-typed-term-list-p tterm-lst options)
    :returns (mv (new-ttl (and (typed-term-list-p new-ttl)
                               (good-typed-term-list-p new-ttl options)))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :measure (list (acl2-count (typed-term-list->term-lst tterm-lst))
                   1)
    (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                            (pseudo-termp path-cond)
                            (pseudo-termp projection)
                            (symbol-listp names)
                            (type-options-p options)
                            (good-typed-term-list-p tterm-lst options))))
          (mv (make-typed-term-list)
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((typed-term-list ttl) tterm-lst)
         ((unless (typed-term-list-consp ttl))
          (mv (make-typed-term-list) ''t names))
         ((mv tt-car proj-car names-car)
          (term-projection (typed-term-list->car ttl options) path-cond
                           projection names options state))
         ((mv ttl-cdr proj-cdr names-cdr)
          (term-list-projection (typed-term-list->cdr ttl options) path-cond
                                projection names-car options state)))
      (mv (typed-term-list->cons tt-car ttl-cdr options)
          `(if ,proj-car ,proj-cdr 'nil)
          names-cdr)))
  )

(verify-guards term-projection)
