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
  (new-fresh-vars 1 current))

;; --------------------------------------------------------------
(defprod projection-triple
  ((term pseudo-termp)
   (new-term pseudo-termp)
   (projection pseudo-termp)))

(defprod projection-list-triple
  ((term-lst pseudo-term-listp)
   (new-term-lst pseudo-term-listp)
   (projection pseudo-termp)))

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

(define new-projection )

(define new-projection-list )

(define generate-fncall-proj ((fn symbolp)
                              (actuals-proj projection-list-triple-p)
                              (aa-map alist-array-map-p))
  :returns (mv (new-term pseudo-termp)
               (new-proj pseudo-termp))
  :guard (not (equal fn 'quote))
  (b* ((term (pseudo-term-fix term))
       (actuals-proj (projection-list-triple-fix actuals-proj))
       ((projection-list-triple a) actuals-proj)
       (actuals a.term-lst)
       (projection a.projection)
       ((unless (mbt (not (equal fn 'quote))))
        (mv `(,fn ,@actuals) projection))
       (aa-map (alist-array-map-fix aa-map))
       (exist? (assoc-equal fn aa-map))
       ((unless exist?)
        (er hard? 'term-projection=>generate-fncall-proj
            "There isn't an alist-array-map item for function ~p0.~%" fn))
       ((equiv eq) (cdr exist?))
       (equiv-thm
        (acl2::meta-extract-formula-w eq.thm (w state)))
       ((unless (pseudo-termp equiv-thm))
        (mv (er hard? 'term-projection=>generate-fncall-proj
                "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
                eq.thm equiv-thm)
            projection))
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
                (yes? (path-test-list projection substed-hypo state))
                ((unless yes?) (mv nil nil nil))
                (equiv-term-substed
                 (term-substitution equiv-term
                                    (pairlis$ fn-equiv-formals new-actuals)
                                    t)))
             (mv t equiv-term-substed `(,equiv-fn (,fn ,@actuals) equiv-term-substed))))
          (& (mv nil nil nil))))
       ((unless ok)
        (er hard? 'term-projection=>generate-fncall-proj
            "Failed to project fncall ~p0 to a new term.~%"
            `(,fn ,@actuals))))
    (mv new-term new-proj)))

(define generate-lambda-proj ((formals-proj projection-list-triple-p)
                              (body-proj projection-triple-p)
                              (actuals-proj projection-list-triple-p))
  :returns (mv new-term new-proj)
  (b* ()
    ()))

(define generate-if-proj ((cond-proj projection-triple-p)
                          (then-proj projection-triple-p)
                          (else-proj projection-triple-p))
  :returns (mv new-term new-proj)
  (b* ((cond-proj (projection-triple-fix cond-proj))
       ((projection-triple cp) cond-proj)
       (then-proj (projection-triple-fix then-proj))
       ((projection-triple tp) then-proj)
       (else-proj (projection-triple-fix else-proj))
       ((projection-triple ep) else-proj)
       (
        (case-match tp.projection
          ))
       (
        (case-match tp.projection
          ))
       )
    ()))

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
        (term-substitution judge `((,old-term . ,new-term)) t))
       ;; there are three types of judgements...
       ((mv new-term &) (generate-fncall-proj ...)))
    new-term))

;; project judgements to using functions for arrays
(define project-judge ((judge pseudo-termp)
                       (old-term pseudo-termp)
                       (new-term pseudo-termp)
                       (projection pseudo-termp)
                       (options type-options-p)
                       state)
  :returns (new-judge pseudo-termp)
  (b* ((judge (pseudo-term-fix judge))
       (old-term (pseudo-term-fix old-term))
       (new-term (pseudo-term-fix new-term))
       (projection (pseudo-term-fix projection))
       (options (type-options-fix options))
       ((type-options to) options)
       ((if (judgement-of-term judge old-term to.supertype))
        (project-one-judge judge old-term new-term projection options))
       ((unless (is-conjunct? judge))
        (er hard? 'term-projection=>project-judgement
            "Judgement should be a conjunct.~%"))
       ((if (equal judge ''t)) ''t)
       ((list & judge-hd judge-tl &) judge)
       (hd-res (project-judge judge-hd old-term new-term projection options)))
    `(if ,hd-res
         ,(project-judge judge-tl old-term new-term projection options)
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
                            (good-typed-term-p new-tt)))
               (new-proj pseudo-termp)
               (new-names symbol-listp))
  :guard (and (good-typed-term-p tterm)
              (equal (typed-term->kind tterm) 'variablep))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (pseudo-termp projection)
                          (symbol-listp names)
                          (type-options-p options)
                          (good-typed-term-p tterm)
                          (equal (typed-term->kind tterm) 'variablep))))
        (mv (make-typed-term)
            (pseudo-term-fix projection)
            (symbol-list-fix names)))
       ((typed-term tt) tterm)
       (the-proj (find-projection tt.term projection))
       ((mv err new-term)
        (case-match the-proj
          (('alist-array-equiv !tt.term new-term) (mv nil new-term))
          (& (mv t nil))))
       ((if err)
        (mv tt ''t names))
       (new-judge (project-judge tt.judgements tt.term new-term the-proj
                                 options state)))
    (mv (make-typed-term :term new-term
                         :path-cond tt.path-cond
                         :judgements new-judge)
        the-proj
        names)))

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
                              (good-typed-term-p new-tt)))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :guard (and (good-typed-term-p tterm)
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
              (symvbol-list-fix names)))
         ((typed-term tt) tterm)
         (formals (lambda-formals (car tt.term)))
         (tta (typed-term-lambda->actuals tterm options))
         (ttb (typed-term-lambda->body tterm options))
         ((typed-term ttt) (typed-term->top tt options))
         (shadowed-path-cond (shadow-path-cond formals path-cond))
         ((mv rtta proja namesa)
          (term-list-projection tta path-cond projection names options state))
         ((typed-term rtta) rtta)
         (new-formals (new-fresh-vars (len formals) (append formals namesa)))
         (namesf (append new-formals namesa))
         (formals-proj (new-projection-list ...))
         (both-actuals (append actuals rtta.term-lst))
         (both-formals (append formals new-formals))
         (substed-proja (term-substitution proja (pairlis$ both-actuals both-formals) t))
         ((mv rttb projb namesb)
          (term-projection ttb shadowed-path-cond substed-proja namesf options state))
         ((mv new-term new-proj)
          (generate-lambda-proj (make-projection-list-triple
                                 :term-lst formals
                                 :new-term-lst new-formals
                                 :projection formals-proj)
                                (make-projection-triple
                                 :term-lst ttb.term
                                 :new-term-lst rttb.term
                                 :projection projb)
                                (make-projection-list-triple
                                 :term-lst tta.term-lst
                                 :new-term-lst rtta.term-lst
                                 :projection proja)))
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
                              (good-typed-term-p new-tt)))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :guard (and (good-typed-term-p tterm)
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
         (ttc (typed-term-if->cond tt options))
         (ttt (typed-term-if->then tt options))
         (tte (typed-term-if->else tt options))
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
         (new-proj (generate-if-proj ...))
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
                              (good-typed-term-p new-tt)))
                 (new-proj pseudo-termp)
                 (new-names symbol-listp))
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'fncallp))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp path-cond)
                            (pseudo-termp projection)
                            (symbol-listp names)
                            (type-options-p options)
                            (good-typed-term-p tterm options))))
          (mv (make-typed-term)
              (pseudo-term-fix projection)
              (symbol-list-fix names)))
         ((type-options to) options)
         ((typed-term tt) tterm)
         ((typed-term-list tta) (typed-term-fncall->actuals tterm to))
         ((typed-term ttt) (typed-term->top tterm to))
         ((cons fn actuals) tt.term)
         ((if (is-alist? fn options))
          ;; do something
          (b* (((unless (and (equal (len actuals 1))
                             (symbolp (car actuals))))
                (prog2$
                 (er hard? 'term-projection=>fncall-projection
                     "We found a alist type recognizer, but its argument is not ~
                     a single variable: ~q0" tt.term)
                 (mv tt projection names)))
               (var (car actuals))
               (fresh-var (new-fresh-var 1 'x names))
               (new-proj-var (new-projection ...))
               ((mv new-term new-proj)
                (generate-fncall-proj fn actuals fresh-var new-proj-var to.aa-map))
               (new-judge (project-judge tt.judgements var fresh-var new-proj
                                         options state)))
            (mv (make-typed-term :term new-term
                                 :path-cond path-cond
                                 :judgements new-judge)
                new-proj
                (cons fresh-var names))))
         (exist? (assoc-equal fn to.aa-map))
         ((mv ptta proja)
          (term-list-projection tta path-cond projection names options))
         ((typed-term ptta) ptta)
         ((mv new-term new-proj)
          (generate-fncall-proj fn
                                (make-projection-list-triple
                                 :term-lst actuals
                                 :new-term-lst ptta.term-lst
                                 :projection proja)
                                to.aa-map))
         (new-top-judge (project-judge ttt.judgements ttt.term new-term new-proj
                                       options state))
         (new-top (make-typed-term :term new-term
                                   :path-cond path-cond
                                   :judgement new-top-judge)))
      (mv (make-typed-fncall new-top ptta to)
          new-proj
          names)))

  (define term-projection ((tterm typed-term-p)
                           (path-cond pseudo-termp)
                           (projection pseudo-termp)
                           (names symbol-listp)
                           (options type-options-p)
                           state)
    :guard (good-typed-term-p tterm)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt)))
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
          (variable-projection tterm path-cond projection names options state))
         ((if (equal (typed-term->kind tterm) 'quotep))
          (change-typed-term tterm :path-cond path-cond))
         ((if (equal (typed-term->kind tterm) 'lambdap))
          (lambda-projection tterm path-cond projection names options state))
         ((if (equal (typed-term->kind tterm) 'ifp))
          (if-projection tterm path-cond projection names options state)))
      (fncall-projection tterm path-cond projection names options state)))

  (define term-list-projection ((tterm-lst typed-term-p)
                                (path-cond pseudo-termp)
                                (projection pseudo-termp)
                                (names symbol-listp)
                                (options type-options-p)
                                state)
    :guard (good-typed-term-list-p tterm-lst)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt)))
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
          (mv ttl ''t names)))
      (mv (typed-term-list->cons tt-car tt-cdr options)
          `(if ,proj-car ,proj-cdr 'nil)
          names)))
  )

(verify-guards term-projection)
