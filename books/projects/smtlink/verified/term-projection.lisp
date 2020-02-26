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
  (acl2::new-symbols-from-base n 'x current))

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
       (new-constraint `(equal ,fresh-var (,a.a2a-fn ,var)))
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
  (local (in-theory (disable pseudo-termp assoc-equal
                             consp-of-pseudo-lambdap
                             pseudo-lambdap-of-fn-call-of-pseudo-termp
                             symbol-listp)))

  (local
   (defthm crock1
     (implies (and (symbol-listp x)
                   (symbol-listp y))
              (symbol-listp (append x y))))
   )

  (local
   (defthm crock2
     (implies (and (pseudo-term-listp x)
                   (pseudo-term-listp y))
              (pseudo-term-listp (append x y))))
   )

  (define generate-fncall-proj ((fn symbolp)
                                (actuals pseudo-term-listp)
                                (new-actuals pseudo-term-listp)
                                (actuals-proj pseudo-termp)
                                (aa-map alist-array-map-p)
                                state)
  :returns (mv (new-term pseudo-termp)
               (new-proj pseudo-termp))
  :guard (not (equal fn 'quote))
  (b* ((fn (symbol-fix fn))
       (actuals (pseudo-term-list-fix actuals))
       (new-actuals (pseudo-term-list-fix new-actuals))
       (actuals-proj (pseudo-term-fix actuals-proj))
       (aa-map (alist-array-map-fix aa-map))
       ((unless (mbt (not (equal fn 'quote))))
        (mv nil nil))
       (exist? (assoc-equal fn aa-map))
       ((unless exist?)
        (mv (er hard? 'term-projection=>generate-fncall-proj
                "There isn't an alist-array-map item for function ~p0.~%" fn)
            nil))
       ((equiv eq) (cdr exist?))
       (equiv-thm
        (acl2::meta-extract-formula-w eq.thm (w state)))
       ((unless (pseudo-termp equiv-thm))
        (mv (er hard? 'term-projection=>generate-fncall-proj
                "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
                eq.thm equiv-thm)
            actuals-proj))
       (fn-formals (strip-cars eq.formal-map))
       (fn-equiv-formals (strip-cdrs eq.formal-map))
       ((mv ok new-term new-proj)
        (case-match equiv-thm
          (('implies hypo (equiv-fn (!fn . !fn-formals) equiv-term))
           (b* (((unless (or (equal equiv-fn 'equal)
                             (equal equiv-fn 'alist-array-equiv)))
                 (mv nil nil nil))
                (both-formals (append fn-formals fn-equiv-formals))
                (both-actuals (append actuals new-actuals))
                (substed-hypo
                 (term-substitution hypo (pairlis$ both-formals both-actuals)
                                    t))
                ;; TODO: need to use both projection and judgements
                (yes? (path-test-list actuals-proj substed-hypo state))
                ((unless yes?) (mv nil nil nil))
                (equiv-term-substed
                 (term-substitution equiv-term
                                    (pairlis$ fn-equiv-formals new-actuals)
                                    t)))
             (mv t equiv-term-substed
                 `(,equiv-fn (,fn ,@actuals) equiv-term-substed))))
          (& (mv nil nil nil))))
       ((unless ok)
        (mv (er hard? 'term-projection=>generate-fncall-proj
                "Failed to project fncall ~p0 to a new term.~%"
                `(,fn ,@actuals))
            nil)))
    (mv new-term new-proj)))
)

(encapsulate ()
  (local (in-theory (disable symbol-listp
                             acl2::pseudo-termp-opener
                             pseudo-term-listp-of-symbol-listp
                             acl2::symbol-listp-when-not-consp
                             consp-of-is-conjunct?)))

(define generate-if-proj ((term pseudo-termp)
                          (new-cond pseudo-termp)
                          (then pseudo-termp)
                          (new-then pseudo-termp)
                          (then-proj pseudo-termp)
                          (else pseudo-termp)
                          (new-else pseudo-termp)
                          (else-proj pseudo-termp)
                          state)
  :returns (mv (new-term pseudo-termp)
               (new-proj pseudo-termp))
  (b* ((term (pseudo-term-fix term))
       (new-cond (pseudo-term-fix new-cond))
       (then (pseudo-term-fix then))
       (new-then (pseudo-term-fix new-then))
       (then-proj (pseudo-term-fix then-proj))
       (else (pseudo-term-fix else))
       (new-else (pseudo-term-fix new-else))
       (else-proj (pseudo-term-fix else-proj))
       (new-term `(if ,new-cond ,new-then ,new-else)))
    (cond ((and (path-test then-proj `(equal ,then ,new-then) state)
                (path-test else-proj `(equal ,else ,new-else) state))
           (mv new-term `(equal ,term ,new-term)))
          ((and (path-test then-proj `(alist-array-equiv ,then ,new-then) state)
                (path-test else-proj `(alist-array-equiv ,else ,new-else) state))
           (mv new-term `(alist-array-equiv ,term ,new-term)))
          (t (mv (er hard? 'term-projection=>if-projection
                     "Inconsistent if projections.~%then: ~p0~% ~
                      else: ~p1~%" then-proj else-proj)
                 nil)))))
)

(define generate-lambda-proj ((term pseudo-termp)
                              (new-formals symbol-listp)
                              (new-actuals pseudo-term-listp)
                              (body pseudo-termp)
                              (new-body pseudo-termp)
                              (body-proj pseudo-termp)
                              state)
  :returns (mv (new-term pseudo-termp)
               (new-proj pseudo-termp))
  :guard (equal (len new-formals)
                (len new-actuals))
  (b* ((term (pseudo-term-fix term))
       (new-formals (symbol-list-fix new-formals))
       (new-actuals (pseudo-term-list-fix new-actuals))
       ((unless (mbt (equal (len new-formals) (len new-actuals))))
        (mv nil nil))
       (body (pseudo-term-fix body))
       (new-body (pseudo-term-fix new-body))
       (body-proj (pseudo-term-fix body-proj))
       (new-term `((lambda ,new-formals ,new-body) ,@new-actuals)))
  (cond ((path-test body-proj `(equal ,body ,new-body) state)
         (mv new-term `(equal ,term ,new-term)))
        ((path-test body-proj `(alist-array-equiv ,body ,new-body) state)
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
                             (projection pseudo-termp)
                             (names symbol-listp)
                             (options type-options-p))
  :returns (mv (new-t pseudo-termp)
               (new-proj pseudo-termp)
               (new-names symbol-listp))
  :guard (and (good-typed-term-p tterm options)
              (equal (typed-term->kind tterm) 'variablep))
  :guard-hints (("Goal" :in-theory (enable typed-term->kind)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (pseudo-termp projection)
                          (symbol-listp names)
                          (type-options-p options)
                          (good-typed-term-p tterm options)
                          (equal (typed-term->kind tterm) 'variablep))))
        (mv nil
            (pseudo-term-fix projection)
            (symbol-list-fix names)))
       ((typed-term tt) tterm)
       (the-proj (find-projection tt.term projection))
       ((unless the-proj) (mv tt.term ''t names))
       ((mv err new-term)
        (case-match the-proj
          (('alist-array-equiv !tt.term new-term) (mv nil new-term))
          (& (mv t nil))))
       ((unless (acl2::variablep new-term))
        (prog2$ (er hard? 'term-projection=>variable-projection
                    "Projecting a variable into a non-variable: ~p0 and ~p1~%"
                    tt.term new-term)
                (mv nil ''t names)))
       ((if err) (mv nil ''t names)))
    (mv new-term the-proj names)))

(local (in-theory (disable (:executable-counterpart typed-term)
                           (:executable-counterpart typed-term-list))))

(local
 (defthm pseudo-term-listp-of-cons
   (implies (and (pseudo-termp x) (pseudo-term-listp y))
            (pseudo-term-listp (cons x y)))))

(defines term-projection
  :well-founded-relation l<
  :verify-guards nil
  :returns-hints (("Goal"
                   :in-theory (disable acl2::pseudo-termp-opener
                                       consp-of-is-conjunct?
                                       binary-append
                                       pseudo-term-listp-of-symbol-listp
                                       acl2::append-when-not-consp
                                       acl2::pseudo-termp-car
                                       pairlis$ default-cdr default-car
                                       acl2::symbol-listp-when-not-consp
                                       symbolp-of-fn-call-of-pseudo-termp
                                       acl2::pseudo-lambdap-of-car-when-pseudo-lambda-listp)))

  (define lambda-projection ((tterm typed-term-p)
                             (projection pseudo-termp)
                             (names symbol-listp)
                             (options type-options-p)
                             state)
    :returns (mv (new-t pseudo-termp)
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'lambdap))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (symbol-listp names)
                            (pseudo-termp projection)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'lambdap))))
          (mv nil
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((typed-term tt) tterm)
         (formals (lambda-formals (car tt.term)))
         ((typed-term-list tta) (typed-term-lambda->actuals tterm options))
         ((typed-term ttb) (typed-term-lambda->body tterm options))
         ((typed-term ttt) (typed-term->top tt options))
         ((mv pta proja namesa)
          (term-list-projection tta projection names options state))
         (new-formals (new-fresh-vars (len formals) (append formals namesa)))
         (namesf (append new-formals namesa))
         (both-actuals (append tta.term-lst pta))
         (both-formals (append formals new-formals))
         (shadowed-proj (shadow-path-cond formals projection))
         (substed-proja
          (term-substitution proja (pairlis$ both-actuals both-formals) t))
         ((mv ptb projb namesb)
          (term-projection ttb `(if ,shadowed-proj ,substed-proja 'nil)
                           namesf options state))
         ((unless (mbt (equal (len new-formals) (len pta))))
          (mv nil nil nil))
         ((mv new-term new-proj)
          (generate-lambda-proj tt.term new-formals pta ttb.term ptb
                                projb state)))
      (mv new-term new-proj namesb)))

  (define if-projection ((tterm typed-term-p)
                         (projection pseudo-termp)
                         (names symbol-listp)
                         (options type-options-p)
                         state)
    :returns (mv (new-t pseudo-termp)
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'ifp))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (symbol-listp names)
                            (pseudo-termp projection)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'ifp))))
          (mv nil
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((typed-term tt) tterm)
         ((typed-term ttc) (typed-term-if->cond tt options))
         ((typed-term ttt) (typed-term-if->then tt options))
         ((typed-term tte) (typed-term-if->else tt options))
         ((typed-term tttop) (typed-term->top tt options))
         ((mv ptc projc namesc)
          (term-projection ttc projection names options state))
         ((mv ptt projt namest)
          (term-projection ttt `(if ,projc ,projection 'nil) namesc options state))
         ((mv pte proje namese)
          (term-projection tte projection namest options state))
         ((mv new-term new-proj)
          (generate-if-proj tt.term ptc ttt.term ptt projt tte.term
                            pte proje state)))
      (mv new-term new-proj namese)))

  (define fncall-projection ((tterm typed-term-p)
                             (projection pseudo-termp)
                             (names symbol-listp)
                             (options type-options-p)
                             state)
    :returns (mv (new-t pseudo-termp)
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'fncallp))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp projection)
                            (symbol-listp names)
                            (type-options-p options)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'fncallp))))
          (mv nil
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((type-options to) options)
         ((typed-term tt) tterm)
         ((typed-term-list tta) (typed-term-fncall->actuals tterm to))
         ((typed-term ttt) (typed-term->top tterm to))
         ((cons fn actuals) tt.term)
         ((if (is-alist? fn options))
          (b* (((unless (and (equal (len actuals) 1)
                             (symbolp (car actuals))))
                (prog2$
                 (er hard? 'term-projection=>fncall-projection
                     "We found a alist type recognizer, but its argument is not ~
                     a single variable: ~q0" tt.term)
                 (mv tt.term projection names)))
               (fresh-var (new-fresh-var names))
               (new-var-proj (new-projection tt.term fresh-var to.alist state))
               ((mv new-term new-proj)
                (generate-fncall-proj fn actuals (list fresh-var) new-var-proj
                                      to.aa-map state)))
            ;; adding array-p info into projection
            (mv new-term `(if ,new-term ,new-proj 'nil)
                (cons fresh-var names))))
         ((mv pta proja namesa)
          (term-list-projection tta projection names options state))
         ((mv new-term new-proj)
          (generate-fncall-proj fn actuals pta proja to.aa-map state)))
      (mv new-term new-proj namesa)))

  (define term-projection ((tterm typed-term-p)
                           (projection pseudo-termp)
                           (names symbol-listp)
                           (options type-options-p)
                           state)
    :guard (good-typed-term-p tterm options)
    :returns (mv (new-t pseudo-termp)
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :measure (list (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp projection)
                            (symbol-listp names)
                            (type-options-p options)
                            (good-typed-term-p tterm options))))
          (mv nil
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((typed-term tt) tterm)
         ((if (equal (typed-term->kind tterm) 'variablep))
          (variable-projection tterm projection names options))
         ((if (equal (typed-term->kind tterm) 'quotep))
          (mv tt.term `(equal ,tt.term ,tt.term) names))
         ((if (equal (typed-term->kind tterm) 'lambdap))
          (lambda-projection tterm projection names options state))
         ((if (equal (typed-term->kind tterm) 'ifp))
          (if-projection tterm projection names options state)))
      (fncall-projection tterm projection names options state)))

  (define term-list-projection ((tterm-lst typed-term-list-p)
                                (projection pseudo-termp)
                                (names symbol-listp)
                                (options type-options-p)
                                state)
    :guard (good-typed-term-list-p tterm-lst options)
    :returns (mv (new-tl pseudo-term-listp)
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :measure (list (acl2-count (typed-term-list->term-lst tterm-lst))
                   1)
    (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                            (pseudo-termp projection)
                            (symbol-listp names)
                            (type-options-p options)
                            (good-typed-term-list-p tterm-lst options))))
          (mv nil
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((typed-term-list ttl) tterm-lst)
         ((unless (typed-term-list-consp ttl))
          (mv nil ''t names))
         ((mv t-car proj-car names-car)
          (term-projection (typed-term-list->car ttl options)
                           projection names options state))
         ((mv t-cdr proj-cdr names-cdr)
          (term-list-projection (typed-term-list->cdr ttl options)
                                projection names-car options state)))
      (mv (cons t-car t-cdr)
          `(if ,proj-car ,proj-cdr 'nil)
          names-cdr)))
  )

(verify-guards term-projection)
