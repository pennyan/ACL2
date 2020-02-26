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

;; --------------------------------------------------------------
(encapsulate ()
  (local (in-theory (disable symbol-listp
                             pseudo-termp
                             pseudo-term-listp)))

(defprod projection-triple
  ((term pseudo-termp)
   (new-term pseudo-termp)
   (projection pseudo-termp)))

(defprod projection-list-triple
  ((term-lst pseudo-term-listp)
   (new-term-lst pseudo-term-listp)
   (projection pseudo-termp)))
)

;; ---------------------------------------------------------------
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
                              (actuals-proj projection-list-triple-p)
                              (aa-map alist-array-map-p)
                              state)
  :returns (mv (new-term pseudo-termp)
               (new-proj pseudo-termp))
  :guard (not (equal fn 'quote))
  (b* ((fn (symbol-fix fn))
       (actuals-proj (projection-list-triple-fix actuals-proj))
       (aa-map (alist-array-map-fix aa-map))
       ((projection-list-triple a) actuals-proj)
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
            a.projection))
       (fn-formals (strip-cars eq.formal-map))
       (fn-equiv-formals (strip-cdrs eq.formal-map))
       ((mv ok new-term new-proj)
        (case-match equiv-thm
          (('implies hypo (equiv-fn (!fn . !fn-formals) equiv-term))
           (b* (((unless (or (equal equiv-fn 'equal)
                             (equal equiv-fn 'alist-array-equiv)))
                 (mv nil nil nil))
                (both-formals (append fn-formals fn-equiv-formals))
                (both-actuals (append a.term-lst a.new-term-lst))
                (substed-hypo
                 (term-substitution hypo (pairlis$ both-formals both-actuals)
                                    t))
                (yes? (path-test-list a.projection substed-hypo state))
                ((unless yes?) (mv nil nil nil))
                (equiv-term-substed
                 (term-substitution equiv-term
                                    (pairlis$ fn-equiv-formals a.new-term-lst)
                                    t)))
             (mv t equiv-term-substed
                 `(,equiv-fn (,fn ,@a.term-lst) equiv-term-substed))))
          (& (mv nil nil nil))))
       ((unless ok)
        (mv (er hard? 'term-projection=>generate-fncall-proj
                "Failed to project fncall ~p0 to a new term.~%"
                `(,fn ,@a.term-lst))
            nil)))
    (mv new-term new-proj)))
)

(define generate-lambda-proj ((formals symbol-listp)
                              (new-formals symbol-listp)
                              (body-proj projection-triple-p)
                              (actuals-proj projection-list-triple-p)
                              state)
  :returns (mv (new-term pseudo-termp)
               (new-proj pseudo-termp))
  :guard (and (equal (len (symbol-list-fix formals))
                     (len (projection-list-triple->term-lst
                           (projection-list-triple-fix actuals-proj))))
              (equal (len (symbol-list-fix new-formals))
                     (len (projection-list-triple->new-term-lst
                           (projection-list-triple-fix actuals-proj)))))
  (b* ((formals (symbol-list-fix formals))
       (new-formals (symbol-list-fix new-formals))
       (body-proj (projection-triple-fix body-proj))
       ((projection-triple bp) body-proj)
       (actuals-proj (projection-list-triple-fix actuals-proj))
       ((projection-list-triple ap) actuals-proj)
       ((unless (mbt (and (equal (len formals)
                                 (len ap.term-lst))
                          (equal (len new-formals)
                                 (len ap.new-term-lst)))))
        (mv nil nil))
       (term `((lambda ,formals ,bp.term) ,@ap.term-lst))
       (new-term `((lambda ,new-formals ,bp.new-term) ,@ap.new-term-lst)))
    (cond ((path-test bp.projection `(equal ,bp.term ,bp.new-term) state)
           (mv new-term `(equal ,term ,new-term)))
          ((path-test bp.projection `(equiv ,bp.term ,bp.new-term) state)
           (mv new-term `(equiv ,term ,new-term)))
          (t (mv (er hard? 'term-projection=>generate-lambda-proj
                     "Inconsistent lambda projections.~%body: ~p0~%"
                     bp)
                 nil)))))

;; There are 8 cases:
;; 1. cond equal, then equal, else equal:
;; new-term = (if cond then else), new-proj = equal
;; 2. cond equal, then equal, else equiv: error
;; 3. cond equal, then equiv, else equal: error
;; 4. cond equal, then equiv, else equiv:
;; new-term = (if cond then else), new-proj = equiv
;; 5. cond equiv, then equal, else equal:
;; new-term = (if cond then else), new-proj = equal
;; 6. cond equiv, then equal, else equiv: error
;; 7. cond equiv, then equiv, else equal: error
;; 8. cond equiv, then equiv, else equiv:
;; new-term = (if cond then else), new-proj = equiv
;;
(define generate-if-proj ((cond-proj projection-triple-p)
                          (then-proj projection-triple-p)
                          (else-proj projection-triple-p)
                          state)
  :returns (new-proj pseudo-termp)
  (b* ((cond-proj (projection-triple-fix cond-proj))
       ((projection-triple cp) cond-proj)
       (then-proj (projection-triple-fix then-proj))
       ((projection-triple tp) then-proj)
       (else-proj (projection-triple-fix else-proj))
       ((projection-triple ep) else-proj)
       (term `(if ,cp.term ,tp.term ,ep.term))
       (new-term `(if ,cp.new-term ,tp.new-term ,ep.new-term)))
    (cond ((and (path-test tp.projection `(equal ,tp.term ,tp.new-term) state)
                (path-test ep.projection `(equal ,ep.term ,ep.new-term) state))
           `(equal ,term ,new-term))
          ((and (path-test tp.projection `(equiv ,tp.term ,tp.new-term) state)
                (path-test ep.projection `(equiv ,ep.term ,ep.new-term) state))
           `(equal ,term ,new-term))
          (t (er hard? 'term-projection=>generate-if-proj
                 "Inconsistent if projections.~%cond: ~p0~%then: ~p1~% ~
                      else: ~p2~%" cp tp ep)))))

(define generate-projection-list-for-single ((actuals pseudo-term-listp)
                                             (the-proj projection-triple-p)
                                             (acc projection-list-triple-p))
  :returns (proj-triple projection-list-triple-p)
  (b* ((actuals (pseudo-term-list-fix actuals))
       (the-proj (projection-triple-fix the-proj))
       (acc (projection-list-triple-fix acc))
       ((projection-triple p) the-proj)
       ((projection-list-triple a) acc)
       ((unless (consp actuals)) a)
       ((cons actuals-hd actuals-tl) actuals)
       ((if (equal actuals-hd p.term))
        (make-projection-list-triple
         :term-lst `(,p.term ,@a.term-lst)
         :new-term-lst `(,p.new-term ,@a.new-term-lst)
         :projection `(if ,p.projection
                          ,a.projection
                        'nil))))
    (generate-projection-list-for-single
     actuals-tl
     the-proj
     (make-projection-list-triple
      :term-lst `(,actuals-hd ,@a.term-lst)
      :new-term-lst `(,actuals-hd ,@a.new-term-lst)
      :projection `(if (equal ,actuals-hd ,actuals-hd)
                       ,a.projection
                     'nil)))))

;; judge is a judgement about old-term. We want to project it into a judgement
;; about new-term.
;; There are two possibilities: old-term and new-term have the projection that
;; they are equal. Note that two terms can be syntactically different but equal
;; according to projection. In that case, we can just do term substitution.
;; Another case is that projection is actually alist-array-equiv. In that case,
;; we use new-projection to generate a new-term.
(define project-one-judge ((judge pseudo-termp)
                           (old-term pseudo-termp)
                           (new-term pseudo-termp)
                           (projection pseudo-termp)
                           (options type-options-p)
                           state)
  :returns (new-judge pseudo-termp)
  :guard (judgement-of-term judge old-term
                            (type-options->supertype options))
  :guard-hints (("Goal" :in-theory (disable symbol-listp acl2::pseudo-termp-car
                                            pseudo-term-listp-of-symbol-listp)))
  (b* ((judge (pseudo-term-fix judge))
       (projection (pseudo-term-fix projection))
       (options (type-options-fix options))
       ((type-options to) options)
       ((mv ok which)
        (case-match projection
          (('equal !old-term !new-term)
           (mv t 'equal))
          (('alist-array-equiv !old-term !new-term)
           (mv t 'equiv))
          (& (mv nil nil))))
       ((unless ok)
        (er hard? 'term-projection=>project-one-judge
            "The projection ~p0 doesn't justify updating the judgement ~p1.~%"
            projection judge))
       ((if (equal which 'equal))
        (term-substitution judge `((,old-term . ,new-term)) t)))
    (cond ((type-predicate-of-term judge old-term to.supertype)
           (b* (((mv new-judge &) (generate-fncall-proj (car judge)
                                                        (make-projection-list-triple
                                                         :term-lst (list old-term)
                                                         :new-term-lst (list new-term)
                                                         :projection projection)
                                                        to.aa-map
                                                        state)))
             new-judge))
          ((single-var-fncall-of-term judge old-term)
           (b* ((proj-list-triple
                 (generate-projection-list-for-single
                  (cdr judge)
                  (projection-triple old-term new-term projection)
                  (make-projection-list-triple)))
                ((mv new-judge &)
                 (generate-fncall-proj (car judge) proj-list-triple to.aa-map state)))
             new-judge))
          ((equal judge old-term) new-term)
          (t (er hard? 'term-projection=>project-one-judge
                 "Judge is malformed: ~p0~%" judge)))))

;; project judgements to using functions for arrays
(define project-judge ((judge pseudo-termp)
                       (old-term pseudo-termp)
                       (new-term pseudo-termp)
                       (projection pseudo-termp)
                       (options type-options-p)
                       state)
  :returns (new-judge pseudo-termp)
  :measure (acl2-count (pseudo-term-fix judge))
  (b* ((judge (pseudo-term-fix judge))
       (old-term (pseudo-term-fix old-term))
       (new-term (pseudo-term-fix new-term))
       (projection (pseudo-term-fix projection))
       (options (type-options-fix options))
       ((type-options to) options)
       ((if (judgement-of-term judge old-term to.supertype))
        (project-one-judge judge old-term new-term projection options state))
       ((unless (is-conjunct? judge))
        (er hard? 'term-projection=>project-judgement
            "Judgement should be a conjunct.~%"))
       ((if (equal judge ''t)) ''t)
       ((list & judge-hd judge-tl &) judge)
       (hd-res (project-judge judge-hd old-term new-term projection options state)))
    `(if ,hd-res
         ,(project-judge judge-tl old-term new-term projection options state)
       'nil)))

;; For a variable, if its judgement says it's an alist, the projection should
;; contain:
;;   (alist-array-equiv the-var new-var)
;; If so, generate new term using new-var, and new judgement by substituting in
;; the new term.
(define variable-projection ((tterm typed-term-p)
                             (projection pseudo-termp)
                             (names symbol-listp)
                             (options type-options-p)
                             state)
  :returns (mv (new-tt (and (typed-term-p new-tt)
                            (good-typed-term-p new-tt options)))
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
        (mv (make-typed-term)
            (pseudo-term-fix projection)
            (symbol-list-fix names)))
       ((typed-term tt) tterm)
       (the-proj (find-projection tt.term projection))
       ((unless the-proj) (mv tt ''t names))
       ((mv err new-term)
        (case-match the-proj
          (('alist-array-equiv !tt.term new-term) (mv nil new-term))
          (& (mv t nil))))
       ((unless (acl2::variablep new-term))
        (prog2$ (er hard? 'term-projection=>variable-projection
                    "Projecting a variable into a non-variable: ~p0 and ~p1~%"
                    tt.term new-term)
                (mv tt ''t names)))
       ((if err) (mv tt ''t names))
       (new-judge (project-judge tt.judgements tt.term new-term the-proj
                                 options state))
       (new-tt (make-typed-term :term new-term
                                :path-cond tt.path-cond
                                :judgements new-judge))
       ((unless (mbt (equal (typed-term->kind new-tt) 'variablep)))
        (mv tt ''t names)))
    (mv new-tt the-proj names)))

(local (in-theory (disable (:executable-counterpart typed-term)
                           (:executable-counterpart typed-term-list))))

(defines term-projection
  :well-founded-relation l<
  :verify-guards nil

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
         (shadowed-path-cond (shadow-path-cond formals path-cond))
         ((mv rtta proja namesa)
          (term-list-projection tta path-cond projection names options state))
         ((typed-term-list rtta) rtta)
         (new-formals (new-fresh-vars (len formals) (append formals namesa)))
         (namesf (append new-formals namesa))
         (both-actuals (append tta.term-lst rtta.term-lst))
         (both-formals (append formals new-formals))
         (substed-actuals-judgements
          (term-substitution rtta.judgements (pairlis$ tta.term-lst formals) t))
         (shadowed-proj (shadow-path-cond formals projection))
         (substed-proja
          (term-substitution proja (pairlis$ both-actuals both-formals) t))
         ((mv rttb projb namesb)
          (term-projection ttb
                           `(if ,shadowed-path-cond
                                ,substed-actuals-judgements
                              'nil)
                           `(if ,shadowed-proj
                                ,substed-proja
                              'nil)
                           namesf options state))
         ((typed-term rttb) rttb)
         ((mv new-term new-proj)
          (generate-lambda-proj formals new-formals
                                (make-projection-triple
                                 :term ttb.term
                                 :new-term rttb.term
                                 :projection projb)
                                (make-projection-list-triple
                                 :term-lst tta.term-lst
                                 :new-term-lst rtta.term-lst
                                 :projection proja)
                                state))
         (new-top-judge (project-judge ttt.judgements ttt.term new-term
                                       new-proj options state))
         (new-top (make-typed-term :term new-term
                                   :path-cond path-cond
                                   :judgements new-top-judge)))
      (mv (make-typed-lambda new-top rttb rtta options)
          new-proj
          namesb)))

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
         ((mv nttc projc namesc)
          (term-projection ttc path-cond projection names options state))
         ((typed-term nttc) nttc)
         ((mv nttt projt namest)
          (term-projection ttt `(if ,(simple-transformer nttc.term) ,path-cond 'nil)
                           `(if ,projc ,projection 'nil) namesc options state))
         ((typed-term nttt) nttt)
         ((mv ntte proje namese)
          (term-projection tte `(if ,(simple-transformer `(not ,nttc.term))
                                    ,path-cond 'nil)
                           projection namest options state))
         ((typed-term ntte) ntte)
         (new-term `(if ,nttc.term ,nttt.term ,ntte.term))
         (new-proj (generate-if-proj (make-projection-triple
                                      :term ttc.term
                                      :new-term nttc.term
                                      :projection projc)
                                     (make-projection-triple
                                      :term ttt.term
                                      :new-term nttt.term
                                      :projection projt)
                                     (make-projection-triple
                                      :term tte.term
                                      :new-term ntte.term
                                      :projection proje)
                                     state))
         (new-top-judge (project-judge tttop.judgements tttop.term new-term new-proj
                                       options state))
         (new-top (make-typed-term :term new-term
                                   :path-cond path-cond
                                   :judgements new-top-judge)))
      (mv (make-typed-if new-top nttc nttt ntte options)
          new-proj
          namese)))

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
         ((if (is-alist? fn options))
          (b* (((unless (and (equal (len actuals) 1)
                             (symbolp (car actuals))))
                (prog2$
                 (er hard? 'term-projection=>fncall-projection
                     "We found a alist type recognizer, but its argument is not ~
                     a single variable: ~q0" tt.term)
                 (mv tt projection names)))
               (var (car actuals))
               (fresh-var (new-fresh-var names))
               (new-proj-var (new-projection tt.term fresh-var to.alist state))
               ((mv new-term new-proj)
                (generate-fncall-proj fn
                                      (make-projection-list-triple
                                       :term-lst actuals
                                       :new-term-lst (list fresh-var)
                                       :projection new-proj-var)
                                      to.aa-map
                                      state))
               (new-top-judge (project-judge ttt.judgements var fresh-var new-proj
                                             options state))
               (new-top (make-typed-term :term new-term
                                         :path-cond path-cond
                                         :judgements new-top-judge)))
            (mv (make-typed-fncall new-top ptta to)
                new-proj
                (cons fresh-var names))))
         ((mv ptta proja namesa)
          (term-list-projection tta path-cond projection names options state))
         ((typed-term-list ptta) ptta)
         ((mv new-term new-proj)
          (generate-fncall-proj fn
                                (make-projection-list-triple
                                 :term-lst actuals
                                 :new-term-lst ptta.term-lst
                                 :projection proja)
                                to.aa-map
                                state))
         (new-top-judge
          (project-judge ttt.judgements ttt.term new-term new-proj options
                         state))
         (new-top (make-typed-term :term new-term
                                   :path-cond path-cond
                                   :judgements new-top-judge)))
      (mv (make-typed-fncall new-top ptta to)
          new-proj
          namesa)))

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
          (mv (make-typed-term)
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((if (equal (typed-term->kind tterm) 'variablep))
          (variable-projection tterm projection names options state))
         ((if (equal (typed-term->kind tterm) 'quotep))
          (mv (change-typed-term tterm :path-cond path-cond)
              projection names))
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
         ((unless (typed-term-list-consp ttl)) (mv ttl projection names))
         ((mv tt-car proj-car names-car)
          (term-projection (typed-term-list->car ttl options)
                           path-cond projection names options state))
         ((typed-term tta) tt-car)
         ((mv tt-cdr proj-cdr names-cdr)
          (term-list-projection (typed-term-list->cdr ttl options)
                                path-cond projection names-car options state))
         ((typed-term ttd) tt-cdr)
         ((unless (mbt (equal tta.path-cond ttd.path-cond)))
          (mv ttl ''t names-cdr)))
      (mv (typed-term-list->cons tt-car tt-cdr options)
          `(if ,proj-car ,proj-cdr 'nil)
          names-cdr)))
  )

(verify-guards term-projection)
