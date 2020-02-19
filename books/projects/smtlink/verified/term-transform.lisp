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
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "basics")
;; (include-book "alist")
(include-book "hint-please")
(include-book "typed-term")
(include-book "type-options")

(set-state-ok t)

;; This clause-processor transforms a term that uses alists into a term that
;; uses arrays. Supposedly other isomorphic transformations can also be made in
;; a similar way.

(define new-fresh-var ((term pseudo-termp))
  :returns (new-var symbolp)
  (b* ((current (acl2::simple-term-vars-lst term)))
    (acl2::new-symbols-from-base 1 'x current)))

;; ---------------------------------------------------------------

(define is-alist-judge ((term pseudo-termp)
                        (judge pseudo-termp)
                        (options type-options-p))
  :returns (a2a maybe-a2a-info-p)
  :measure (acl2-count (pseudo-term-fix judge))
  (b* ((judge (pseudo-term-fix judge))
       (options (type-options-fix options))
       ((type-options to) options)
       ((if (type-predicate-of-term judge term to.supertype))
        (is-alist? (car judge) options))
       ((unless (is-conjunct? judge)) nil)
       ((if (equal judge ''t)) nil)
       ((list & judge-hd judge-tl &) judge)
       (hd-res (is-alist-judge term judge-hd options))
       ((if hd-res) hd-res))
    (is-alist-judge term judge-tl options)))

;; find the alist-array-equiv of term from projection
(define find-projection ((term pseudo-termp) (projection pseudo-termp)))

(define project-one-judge ((judge pseudo-termp)
                           (old-term pseudo-termp)
                           (new-term pseudo-termp)
                           (projection pseudo-termp)
                           (options type-options-p)
                           state)
  :returns (new-judge pseudo-termp)
  :guard (type-predicate-of-term judge old-term
                                 (type-options->supertype options))
  (b* ((judge (pseudo-term-fix judge))
       (projection (pseudo-term-fix projection))
       (options (type-options-fix options))
       ((type-options to) options)
       (yes?
        (path-test projection `(alist-array-equiv ,old-term ,new-term) state))
       ((unless yes?) judge)
       ((cons fn actuals) judge)
       (exist? (assoc-equal fn to.aa-map))
       ??
       )
    ()))

;; project judgements to using functions for arrays
(define project-judgement ((judge pseudo-termp)
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
       ((if (type-predicate-of-term judge old-term to.supertype))
        (project-one-judge judge old-term new-term projection options))
       ((unless (is-conjunct? judge))
        (er hard? 'term-transform=>project-judgement
            "Judgement should be a conjunct.~%"))
       ((if (equal judge ''t)) ''t)
       ((list & judge-hd judge-tl &) judge)
       (hd-res (project-judgement judge-hd old-term new-term projection options)))
    `(if ,hd-res
         ,(project-judgement judge-tl old-term new-term projection options)
       'nil))
  )

;; ---------------------------------------------------------------

;; For a variable, if its judgement says it's an alist, the projection should
;; contain:
;;   (alist-array-equiv the-var new-var)
;; If so, generate new term using new-var, and new judgement by substituting in
;; the new term.
(define variable-transform ((tterm typed-term-p)
                            (projection pseudo-termp)
                            (options type-options-p)
                            state)
  :returns (mv (new-tt (and (typed-term-p new-tt)
                            (good-typed-term-p new-tt)))
               (new-proj pseudo-termp))
  :guard (and (good-typed-term-p tterm)
              (equal (typed-term->kind tterm) 'variablep))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (pseudo-termp projection)
                          (type-options-p options)
                          (good-typed-term-p tterm)
                          (equal (typed-term->kind tterm) 'variablep))))
        (mv (make-typed-term)
            (pseudo-term-fix projection)))
       ((typed-term tt) tterm)
       (the-proj (find-projection tt.term projection))
       ((mv err new-term)
        (case-match the-proj
          (('alist-array-equiv !tt.term new-term) (mv nil new-term))
          (& (mv t nil))))
       ((if err)
        (mv tt `(equal tt.term tt.term)))
       (new-judge (project-judgements tt.judgements tt.term new-term projection
                                      options state)))
    (mv (make-typed-term :term new-term
                         :path-cond tt.path-cond
                         :judgements new-judge)
        the-proj)))

(defines term-transform
  :well-founded-relation l<
  :verify-guards nil

  (defin lambda-transform ((tterm typed-term-p)
                           (projection pseudo-termp)
                           (options type-options-p)
                           state)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt)))
                 (new-proj pseudo-termp))
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'lambdap))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* ()
      ()))

  (defin if-transform ((tterm typed-term-p)
                       (projection pseudo-termp)
                       (options type-options-p)
                       state)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt)))
                 (new-proj pseudo-termp))
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'ifp))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp projection)
                            (type-options-p options)
                            (pseudo-termp projection)
                            (good-typed-term-p tterm options)
                            (equal (typed-term->kind tterm) 'ifp))))
          (mv (make-typed-term)
              (pseudo-term-fix projection)))
         ((typed-term tt) tterm)
         (ttc (typed-term-if->cond tt options))
         (ttt (typed-term-if->then tt options))
         (tte (typed-term-if->else tt options))
         ((typed-term tttop) (typed-term->top tt options))

         ((mv nttc projc) (term-transform ttc projection options state))
         ((typed-term nttc) nttc)
         ((mv nttt projt)
          (term-transform ttt `(if ,projc ,projection 'nil) options state))
         ((typed-term nttt) nttt)
         ((mv ntte proje)
          (term-transform tte projection options state))
         ((typed-term ntte) ntte)
         (new-top (make-typed-term :term `(if ,nttc.term ,nttt.term ,ntte.term)
                                   :path-cond tttop.path-cond))
         (new-proj ))
      (mv (make-typed-if new-top nttc nttt ntte options)
          new-proj)))

  ;; If fn is an alist recognizer, introduce a fresh var, add the equality and
  ;; introduce alist-array-equiv relationship into the projection. Return the
  ;; projection. New term should be (array-p x) and its judgements should be
  ;; updated accordingly.
  ;; If fn is an alist operator, check if projection has enough hypotheses to
  ;; conclude the alist-array-equiv relation. If so, update the term and
  ;; judgements and projection.
  ;; If fn is a basic function, generate a projection.
  ;; If fn is user-defined, expand; if expansion depth reaches 0, use the
  ;; projection to discharge the alist-array-equiv between fn and smt-fn. Update
  ;; the term and judgements.
  (defin fncall-transform ((tterm typed-term-p)
                           (projection pseudo-termp)
                           (options type-options-p)
                           state)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt)))
                 (new-proj pseudo-termp))
    :guard (and (good-typed-term-p tterm)
                (equal (typed-term->kind tterm) 'fncallp))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* ()
      ()))

  (define term-transform ((tterm typed-term-p)
                          (projection pseudo-termp)
                          (options type-options-p)
                          state)
    :guard (good-typed-term-p tterm)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt)))
                 (new-proj pseudo-termp))
    :measure (list (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (pseudo-termp projection)
                            (good-typed-term-p tterm options))))
          (mv (make-typed-term)
              (pseudo-term-fix projection)))
         ((if (equal (typed-term->kind tterm) 'variablep))
          (variable-transform tterm projection options state))
         ((if (equal (typed-term->kind tterm) 'quotep)) tterm)
         ((if (equal (typed-term->kind tterm) 'lambdap))
          (lambda-transform tterm projection options state))
         ((if (equal (typed-term->kind tterm) 'ifp))
          (if-transform tterm projection options state)))
      (fncall-transform tterm projection options state)))

  (define term-list-transform ((tterm-lst typed-term-p)
                               (projection pseudo-termp)
                               (options type-options-p)
                               state)
    :guard (good-typed-term-list-p tterm-lst)
    :returns (mv (new-tt (and (typed-term-p new-tt)
                              (good-typed-term-p new-tt)))
                 (new-proj pseudo-termp))
    :measure (list (acl2-count (typed-term-list->term-lst tterm-lst))
                   1)
    (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                            (type-options-p options)
                            (pseudo-termp projection)
                            (good-typed-term-list-p tterm-lst options))))
          (mv (make-typed-term-list)
              (pseudo-term-fix projection)))
         ((typed-term-list ttl) tterm-lst)
         ((unless (typed-term-list-consp ttl)) (mv ttl ''t))
         ((mv tt-car proj-car)
          (term-transform (typed-term-list->car ttl options)
                          projection options state))
         ((typed-term tta) tt-car)
         ((mv tt-cdr proj-cdr)
          (term-list-transform
           (typed-term-list->cdr ttl options) projection options state))
         ((typed-term ttd) tt-cdr)
         ((unless (mbt (equal tta.path-cond ttd.path-cond)))
          (mv ttl ''t)))
      (mv (typed-term-list->cons tt-car tt-cdr options)
          `(if ,proj-car ,proj-cdr 'nil))))
  )

(verify-guards term-transform)
