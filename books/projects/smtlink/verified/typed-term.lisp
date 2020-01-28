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

(include-book "../utils/pseudo-term")
(include-book "path-cond")
;; (include-book "evaluator")

;; reduce not's in term
(define simple-transformer ((term pseudo-termp))
  :returns (new-term pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (new-term
        (case-match term
          (('not ('not term1)) term1)
          (& term))))
    new-term))

(encapsulate ()
  (local (in-theory (disable pseudo-termp)))

  (defprod typed-term
    ((term pseudo-termp :default ''nil)
     (path-cond pseudo-termp :default ''t)
     (judgements pseudo-termp :default '(if (if (symbolp 'nil)
                                                (if (booleanp 'nil) 't 'nil)
                                              'nil)
                                            't
                                          'nil))))

  (defprod typed-term-list
    ((term-lst pseudo-term-listp :default nil)
     (path-cond pseudo-termp :default ''t)
     (judgements pseudo-termp :default ''t)))
  )

(define typed-term-list-consp ((tterm-lst typed-term-list-p))
  :returns (ok booleanp)
  (b* ((tterm-lst (typed-term-list-fix tterm-lst))
       ((typed-term-list ttl) tterm-lst))
    (consp ttl.term-lst))
  ///
  (more-returns
   (ok (implies (and (typed-term-list-p tterm-lst) ok)
                (consp (typed-term-list->term-lst tterm-lst)))
       :name consp-of-term-lst-of-typed-term-list-consp)))

;; ---------------------------------------------
;;       Recognizers

(define typed-term->kind ((tterm typed-term-p))
  :returns (kind symbolp)
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
       ((if (acl2::variablep tt.term)) 'variablep)
       ((if (acl2::quotep tt.term)) 'quotep)
       ((cons fn &) tt.term)
       ((if (pseudo-lambdap fn)) 'lambdap)
       ((if (equal fn 'if)) 'ifp))
    'fncallp)
  ///
  (more-returns
   (kind (member-equal kind '(variablep quotep lambdap ifp fncallp))
         :name range-of-typed-term->kind)
   (kind (implies (and (typed-term-p tterm)
                       (not (equal kind 'variablep))
                       (not (equal kind 'quotep))
                       (not (equal kind 'lambdap))
                       (not (equal kind 'ifp)))
                  (equal kind 'fncallp))
         :name cases-of-typed-term->kind)
   (kind (implies (equal kind 'variablep)
                  (acl2::variablep (typed-term->term tterm)))
         :name implies-of-variable-kind)
   (kind (implies (equal kind 'quotep)
                  (acl2::quotep (typed-term->term tterm)))
         :name implies-of-quote-kind)
   (kind (implies (equal kind 'lambdap)
                  (and (consp (typed-term->term tterm))
                       (pseudo-lambdap (car (typed-term->term tterm)))))
         :name implies-of-lambda-kind)
   (kind (implies (equal kind 'ifp)
                  (and (consp (typed-term->term tterm))
                       (equal (car (typed-term->term tterm)) 'if)))
         :name implies-of-if-kind)
   (kind (implies (equal kind 'fncallp)
                  (and (consp (typed-term->term tterm))
                       (not (equal (car (typed-term->term tterm)) 'quote))
                       (symbolp (car (typed-term->term tterm)))))
         :name implies-of-fncall-kind)
   (kind (implies (equal kind x)
                  (equal (typed-term->kind
                          (typed-term (typed-term->term tterm) a b))
                         x))
         :name kind-preserved)))

(define good-typed-variable-p ((tterm typed-term-p)
                               (options type-options-p))
  :returns (ok booleanp)
  (b* ((tterm (typed-term-fix tterm))
       (options (type-options-fix options))
       ((typed-term tt) tterm)
       ((type-options to) options))
    (if (is-conjunct-list? tt.judgements tt.term to.supertype) t nil)))

#|
(good-typed-variable-p (typed-term 'x
                                   ''t
                                   '(if (if (booleanp (rational-integer-alistp x))
                                            't
                                          'nil)
                                        (if (if 't 't 'nil) 't 'nil)
                                      'nil)))
|#

(define good-typed-quote-p ((tterm typed-term-p)
                            (options type-options-p))
  :returns (ok booleanp)
  (b* ((tterm (typed-term-fix tterm))
       (options (type-options-fix options))
       ((typed-term tt) tterm)
       ((type-options to) options))
    (if (is-conjunct-list? tt.judgements tt.term to.supertype) t nil)))

#|
(good-typed-quote-p (typed-term ''t
                                ''t
                                '(if (if (symbolp 't)
                                         (if (booleanp 't) 't 'nil)
                                       'nil)
                                     't
                                   'nil)))
|#

(defines good-typed-term
  :well-founded-relation l<
  :verify-guards nil
  :hints (("Goal"
           :in-theory (disable pseudo-termp
                               equal-fixed-and-x-of-pseudo-termp
                               symbol-listp
                               pseudo-term-listp
                               acl2::pseudo-termp-cadr-from-pseudo-term-listp)))

  (define good-typed-lambda-p ((tterm typed-term-p)
                               (options type-options-p))
    :returns (ok booleanp)
    :guard (and (consp (typed-term->term tterm))
                (pseudo-lambdap (car (typed-term->term tterm))))
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   0)
    (b* ((tterm (typed-term-fix tterm))
         (options (type-options-fix options))
         ((typed-term tt) tterm)
         ((type-options to) options)
         ((unless (mbt (and (consp tt.term)
                            (pseudo-lambdap (car tt.term)))))
          nil)
         ((cons fn actuals) tt.term)
         (formals (lambda-formals fn))
         (body (lambda-body fn))
         ((unless (consp tt.judgements)) nil)
         (match?
          (case-match tt.judgements
            (('if return-judge
                 ('if (('lambda !formals body-judge) . !actuals)
                     actuals-judge
                   ''nil)
               ''nil)
             (and (is-conjunct-list? return-judge tt.term to.supertype)
                  (good-typed-term-list-p
                   (make-typed-term-list :term-lst actuals
                                         :path-cond tt.path-cond
                                         :judgements actuals-judge)
                   to)
                  (b* ((shadowed-path-cond (shadow-path-cond formals tt.path-cond)))
                    (good-typed-term-p
                     (make-typed-term :term body
                                      :path-cond shadowed-path-cond
                                      :judgements body-judge)
                     to))))
            (& nil))))
      (if match? t nil)))

  (define good-typed-if-p ((tterm typed-term-p)
                           (options type-options-p))
    :returns (ok booleanp)
    :guard (and (consp (typed-term->term tterm))
                (equal (car (typed-term->term tterm)) 'if))
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   0)
    (b* ((tterm (typed-term-fix tterm))
         (options (type-options-fix options))
         ((typed-term tt) tterm)
         ((type-options to) options)
         ((unless (mbt (and (consp tt.term)
                            (equal (car tt.term) 'if))))
          nil)
         ((unless (equal (len (cdr tt.term)) 3))
          (er hard? 'typed-term=>good-typed-if-p
              "Malformed if term: ~q0" tt.term))
         ((list & cond then else) tt.term)
         ((unless (consp tt.judgements)) nil)
         (match?
          (case-match tt.judgements
            (('if judge-if-top
                 ('if judge-cond
                     ('if !cond judge-then judge-else)
                   ''nil)
               ''nil)
             (b* ((- (cw "cond: ~p0, path-cond: ~p1, judge-cond: ~p2~%"
                         cond tt.path-cond judge-cond))
                  (- (cw "then: ~p0, path-cond: ~p1, judge-then: ~p2~%"
                         then `(if ,(simple-transformer cond)
                                   ,tt.path-cond 'nil)
                         judge-then))
                  (- (cw "else: ~p0, path-cond: ~p1, judge-else: ~p2~%"
                         else `(if ,(simple-transformer `(not ,cond))
                                   ,tt.path-cond 'nil)
                         judge-else)))
               (and (is-conjunct-list? tt.term judge-if-top to.supertype)
                    (good-typed-term-p
                     (make-typed-term :term cond
                                      :path-cond tt.path-cond
                                      :judgements judge-cond)
                     to)
                    (good-typed-term-p
                     (make-typed-term :term then
                                      :path-cond
                                      `(if ,(simple-transformer cond)
                                           ,tt.path-cond 'nil)
                                      :judgements judge-then)
                     to)
                    (good-typed-term-p
                     (make-typed-term :term else
                                      :path-cond
                                      `(if ,(simple-transformer `(not ,cond))
                                           ,tt.path-cond 'nil)
                                      :judgements judge-else)
                     to))))
            (& nil))))
      (if match? t nil)))

  (define good-typed-fncall-p ((tterm typed-term-p)
                               (options type-options-p))
    :returns (ok booleanp)
    :guard (and (consp (typed-term->term tterm))
                (not (equal (car (typed-term->term tterm)) 'quote))
                (symbolp (car (typed-term->term tterm))))
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   0)
    (b* ((tterm (typed-term-fix tterm))
         ((typed-term tt) tterm)
         ((unless (mbt (consp tt.term))) nil)
         ((cons & actuals) tt.term)
         ((unless (consp tt.judgements)) nil)
         (match?
          (case-match tt.judgements
            (('if return-judge actuals-judge ''nil)
             (b* ((- (cw "return-judge: ~q0" return-judge))
                  (- (cw "actuals: ~p0, path-cond: ~p1, actuals-judge: ~p2~%"
                         actuals tt.path-cond actuals-judge)))
               (and (good-typed-term-list-p
                     (make-typed-term-list :term-lst actuals
                                           :path-cond tt.path-cond
                                           :judgements actuals-judge)
                     options))))
            (& nil))))
      (if match? t nil)))

  (define good-typed-term-p ((tterm typed-term-p)
                             (options type-options-p))
    :returns (ok booleanp)
    :measure (list (acl2-count
                    (typed-term->term
                     (typed-term-fix tterm)))
                   1)
    (b* ((tterm (typed-term-fix tterm))
         ((typed-term tt) tterm)
         ((if (equal (typed-term->kind tt) 'variablep))
          (good-typed-variable-p tt options))
         ((if (equal (typed-term->kind tt) 'quotep))
          (good-typed-quote-p tt options))
         ((if (equal (typed-term->kind tt) 'lambdap))
          (good-typed-lambda-p tt options))
         ((if (equal (typed-term->kind tt) 'ifp))
          (good-typed-if-p tt options)))
      (good-typed-fncall-p tt options)))

  (define good-typed-term-list-p ((tterm-lst typed-term-list-p)
                                  (options type-options-p))
    :returns (ok booleanp)
    :measure (list (acl2-count
                    (typed-term-list->term-lst
                     (typed-term-list-fix tterm-lst)))
                   1)
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((typed-term-list ttl) tterm-lst)
         ((unless (is-conjunct? ttl.judgements))
          (er hard? 'typed-term=>good-typed-term-list-p
              "Judgements ~p0 is not a conjunct.~%" ttl.judgements))
         ((if (and (null ttl.term-lst) (equal ttl.judgements ''t))) t)
         ((unless (consp ttl.term-lst))
          (er hard? 'typed-term=>good-typed-term-list-p
              "Term runs out but there are judgements left ~p0.~%"
              ttl.judgements))
         ((if (equal ttl.judgements ''t))
          (er hard? 'typed-term=>good-typed-term-list-p
              "Judgements runs out but there are terms left ~p0.~%"
              ttl.term-lst))
         ((cons term-hd term-tl) ttl.term-lst)
         ((mv err judge-hd judge-tl)
          (case-match ttl.judgements
            (('if judge-hd judge-tl ''nil)
             (mv nil judge-hd judge-tl))
            (& (mv t nil nil))))
         ((if err)
          (er hard? 'typed-term=>good-typed-term-list-p
              "Malformed typed-term-list: ~p0~%"
              ttl.term-lst)))
      (and (good-typed-term-p
            (make-typed-term :term term-hd
                             :path-cond ttl.path-cond
                             :judgements judge-hd)
            options)
           (good-typed-term-list-p
            (make-typed-term-list :term-lst term-tl
                                  :path-cond ttl.path-cond
                                  :judgements judge-tl)
            options))))
  ///
   (defthm good-typed-variable-p-of-good-term
     (implies (and (typed-term-p tterm)
                   (equal (typed-term->kind tterm) 'variablep))
              (iff (good-typed-term-p tterm options)
                   (good-typed-variable-p tterm options))))
   (defthm good-typed-quote-p-of-good-term
     (implies (and (typed-term-p tterm)
                   (equal (typed-term->kind tterm) 'quotep))
              (iff (good-typed-term-p tterm options)
                   (good-typed-quote-p tterm options))))
   (defthm good-typed-lambda-p-of-good-term
     (implies (and (typed-term-p tterm)
                   (equal (typed-term->kind tterm) 'lambdap))
              (iff (good-typed-term-p tterm options)
                   (good-typed-lambda-p tterm options))))
   (defthm good-typed-if-p-of-good-term
     (implies (and (typed-term-p tterm)
                   (equal (typed-term->kind tterm) 'ifp))
              (iff (good-typed-term-p tterm options)
                   (good-typed-if-p tterm options))))
   (defthm good-typed-fncall-p-of-good-term
     (implies (and (typed-term-p tterm)
                   (equal (typed-term->kind tterm) 'fncallp))
              (iff (good-typed-term-p tterm options)
                   (good-typed-fncall-p tterm options))))
  )

(local (in-theory (disable pseudo-termp
                           symbol-listp
                           acl2::pseudo-termp-opener
                           pseudo-term-listp-of-symbol-listp)))

(verify-guards good-typed-term-p)

(defthm good-typed-term-of-make-typed-term
  (good-typed-term-p (make-typed-term) options)
  :hints (("Goal" :in-theory (enable good-typed-term-p
                                     good-typed-quote-p
                                     is-conjunct-list?
                                     judgement-of-term))))

(defthm good-typed-term-list-of-make-typed-term-list
  (good-typed-term-list-p (make-typed-term-list) options)
  :hints (("Goal" :in-theory (enable good-typed-term-list-p))))

;; -------------------------------------------------------------------
;; Theorems for destructors
;; TODO: simplify the proof

(defthm implies-of-good-typed-if
  (implies (and (typed-term-p tterm) (type-options-p options)
                (good-typed-if-p tterm options))
           (and (consp (cdr (typed-term->term tterm)))
                (consp (cddr (typed-term->term tterm)))
                (consp (cdddr (typed-term->term tterm)))
                (consp (typed-term->judgements tterm))
                (consp (cdr (typed-term->judgements tterm)))
                (consp (cddr (typed-term->judgements tterm)))
                (consp (caddr (typed-term->judgements tterm)))
                (consp (cdddr (typed-term->judgements tterm)))
                (not (cddddr (typed-term->judgements tterm)))
                (consp (cdr (caddr (typed-term->judgements tterm))))
                (consp (cddr (caddr (typed-term->judgements tterm))))
                (consp (caddr (caddr (typed-term->judgements tterm))))
                (consp (cddr (caddr (caddr (typed-term->judgements tterm)))))
                (consp (cdr (caddr (caddr (typed-term->judgements tterm)))))
                (consp (cdddr (caddr (typed-term->judgements tterm))))
                (not (cddddr (caddr (typed-term->judgements tterm))))
                (consp (cdddr (caddr (caddr (typed-term->judgements tterm)))))
                (not (cddddr (caddr (caddr (typed-term->judgements tterm)))))
                (pseudo-termp (cadr (caddr (typed-term->judgements tterm))))
                (good-typed-term-p
                 (typed-term (cadr (typed-term->term tterm))
                             (typed-term->path-cond tterm)
                             (cadr (caddr (typed-term->judgements tterm))))
                 options)
                (good-typed-term-p
                 (typed-term (caddr (typed-term->term tterm))
                             (list* 'if
                                    (simple-transformer (cadr (typed-term->term tterm)))
                                    (typed-term->path-cond tterm)
                                    '('nil))
                             (caddr (caddr (caddr (typed-term->judgements
                                                   tterm)))))
                 options)
                (good-typed-term-p
                 (typed-term
                  (cadddr (typed-term->term tterm))
                  (list* 'if
                         (simple-transformer (list 'not
                                                   (cadr (typed-term->term tterm))))
                         (typed-term->path-cond tterm)
                         '('nil))
                  (cadddr (caddr (caddr (typed-term->judgements tterm)))))
                 options)
                (pseudo-termp (caddr (caddr (caddr (typed-term->judgements
                                                    tterm)))))
                (pseudo-termp (cadddr (caddr (caddr (typed-term->judgements
                                                     tterm)))))))
  :hints (("Goal"
           :expand (good-typed-if-p tterm options))))

(defthm implies-of-good-typed-fncall
  (implies (and (typed-term-p tterm) (type-options-p options)
                (good-typed-fncall-p tterm options))
           (and (consp (typed-term->judgements tterm))
                (consp (cdr (typed-term->judgements tterm)))
                (consp (cddr (typed-term->judgements tterm)))
                (pseudo-termp (caddr (typed-term->judgements tterm)))
                (good-typed-term-list-p
                 (typed-term-list (cdr (typed-term->term tterm))
                                  (typed-term->path-cond tterm)
                                  (caddr (typed-term->judgements tterm)))
                 options)))
  :hints (("Goal"
           :expand (good-typed-fncall-p tterm options))))

(defthm implies-of-good-typed-lambda
  (implies (and (typed-term-p tterm) (type-options-p options)
                (good-typed-lambda-p tterm options))
           (and (consp (typed-term->judgements tterm))
                (consp (cdr (typed-term->judgements tterm)))
                (consp (caddr (typed-term->judgements tterm)))
                (consp (cddr (typed-term->judgements tterm)))
                (consp (cdddr (typed-term->judgements tterm)))
                (consp (cdr (caddr (typed-term->judgements tterm))))
                (consp (cddr (caddr (typed-term->judgements tterm))))
                (consp (cadr (caddr (typed-term->judgements tterm))))
                (consp (car (cadr (caddr (typed-term->judgements tterm)))))
                (consp (cdddr (caddr (typed-term->judgements tterm))))
                (consp (cdr (car (cadr (caddr (typed-term->judgements
                                               tterm))))))
                (consp (cddr (car (cadr (caddr (typed-term->judgements tterm))))))
                (not (cddddr (typed-term->judgements tterm)))
                (not (cddddr (caddr (typed-term->judgements tterm))))
                (not (cdddr (car (cadr (caddr (typed-term->judgements tterm))))))
                (pseudo-termp (caddr (caddr (typed-term->judgements tterm))))
                (pseudo-termp (caddr (car (cadr (caddr (typed-term->judgements
                                                        tterm))))))
                (good-typed-term-list-p
                 (typed-term-list (cdr (typed-term->term tterm))
                                  (typed-term->path-cond tterm)
                                  (caddr (caddr (typed-term->judgements
                                                 tterm))))
                 options)
                (good-typed-term-p
                 (typed-term (caddr (car (typed-term->term tterm)))
                             (shadow-path-cond (cadr (car (typed-term->term tterm)))
                                               (typed-term->path-cond tterm))
                             (caddr (car (cadr (caddr (typed-term->judgements
                                                       tterm))))))
                 options)))
  :hints (("Goal"
           :expand (good-typed-lambda-p tterm options))))

(defthm implies-of-good-typed-term-list
  (implies (and (typed-term-list-p tterm-lst)
                (type-options-p options)
                (good-typed-term-list-p tterm-lst options)
                (typed-term-list-consp tterm-lst))
           (and (consp (typed-term-list->judgements tterm-lst))
                (pseudo-termp (cadr (typed-term-list->judgements tterm-lst)))
                (not (cddddr (typed-term-list->judgements tterm-lst)))
                (consp (cddr (typed-term-list->judgements tterm-lst)))
                (consp (cdr (typed-term-list->judgements tterm-lst)))
                (consp (cdddr (typed-term-list->judgements tterm-lst)))
                (pseudo-termp (caddr (typed-term-list->judgements tterm-lst)))
                (good-typed-term-p
                 (typed-term (car (typed-term-list->term-lst tterm-lst))
                             (typed-term-list->path-cond tterm-lst)
                             (cadr (typed-term-list->judgements tterm-lst)))
                 options)
                (good-typed-term-list-p
                 (typed-term-list (cdr (typed-term-list->term-lst tterm-lst))
                                  (typed-term-list->path-cond tterm-lst)
                                  (caddr (typed-term-list->judgements
                                          tterm-lst)))
                 options)))
  :hints (("Goal" :expand ((good-typed-term-list-p tterm-lst options)
                           (typed-term-list-consp tterm-lst)))))

;; ---------------------------------------------
;;       Destructors for typed-terms

(local (in-theory (disable (:executable-counterpart typed-term)
                           (:executable-counterpart typed-term-list))))

;; ifp destructors
(define typed-term-ifp->cond ((tterm typed-term-p)
                              (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm options))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'ifp)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       (cond-term (cadr tt.term))
       (cond-path-cond tt.path-cond)
       ((mv err cond-judgements)
        (case-match tt.judgements
          ((& & (& judge-cond . &) &)
           (mv nil judge-cond))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-ifp->cond
            "Malformed if judgements ~q0" tt.judgements)))
    (make-typed-term :term cond-term
                     :path-cond cond-path-cond
                     :judgements cond-judgements)))

(define typed-term-ifp->then ((tterm typed-term-p)
                              (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm options))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'ifp)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((list* & cond then-term &) tt.term)
       (then-path-cond `(if ,(simple-transformer cond)
                            ,tt.path-cond 'nil))
       ((mv err then-judgements)
        (case-match tt.judgements
          ((& & (& & (& & judge-then . &) &) &)
           (mv nil judge-then))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-ifp->then
            "Malformed if judgements ~q0" tt.judgements)))
    (make-typed-term :term then-term
                     :path-cond then-path-cond
                     :judgements then-judgements)))

(define typed-term-ifp->else ((tterm typed-term-p)
                              (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm options))
  :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'ifp)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((list & cond & else-term) tt.term)
       (else-path-cond `(if ,(simple-transformer `(not ,cond))
                            ,tt.path-cond 'nil))
       ((mv err else-judgements)
        (case-match tt.judgements
          ((& & (& & (& & & judge-else) &) &)
           (mv nil judge-else))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-ifp->else
            "Malformed if judgements ~q0" tt.judgements)))
    (make-typed-term :term else-term
                     :path-cond else-path-cond
                     :judgements else-judgements)))

;; fncallp destructors
(define typed-term-fncallp->actuals ((tterm typed-term-p)
                                     (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'fncallp)
              (good-typed-term-p tterm options))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'fncallp)
                          (good-typed-term-p tterm options))))
        (make-typed-term-list))
       ((typed-term tt) tterm)
       ((cons & actuals) tt.term)
       ((mv err actuals-judgements)
        (case-match tt.judgements
          ((& & actuals-judge . &)
           (mv nil actuals-judge))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-fncall->actuals
            "Malformed fncall judgements ~q0" tt.judgements)))
    (make-typed-term-list :term-lst actuals
                          :path-cond tt.path-cond
                          :judgements actuals-judgements)))

;; lambdap destructors
(define typed-term-lambdap->actuals ((tterm typed-term-p)
                                     (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'lambdap)
              (good-typed-term-p tterm options))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'lambdap)
                          (good-typed-term-p tterm options))))
        (make-typed-term-list))
       ((typed-term tt) tterm)
       ((cons & actuals) tt.term)
       ((mv err actuals-judgements)
        (case-match tt.judgements
          ((& & (& & actuals-judge . &) &)
           (mv nil actuals-judge))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-lambda->actuals
            "Malformed lambda judgements ~q0" tt.judgements)))
    (make-typed-term-list :term-lst actuals
                          :path-cond tt.path-cond
                          :judgements actuals-judgements)))

(define typed-term-lambdap->body ((tterm typed-term-p)
                                  (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'lambdap)
              (good-typed-term-p tterm options))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'lambdap)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((cons fn &) tt.term)
       (formals (lambda-formals fn))
       (body (lambda-body fn))
       (shadowed-path-cond (shadow-path-cond formals tt.path-cond))
       ((mv err body-judgements)
        (case-match tt.judgements
          ((& & (& ((& & body-judge) . &) & &) &)
           (mv nil body-judge))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-lambda->body
            "Malformed lambda judgements ~q0" tt.judgements)))
    (make-typed-term :term body
                     :path-cond shadowed-path-cond
                     :judgements body-judgements)))

;; typed-term-list
(define typed-term-list->car ((tterm-lst typed-term-list-p)
                              (options type-options-p))
  :guard (and (good-typed-term-list-p tterm-lst options)
              (typed-term-list-consp tterm-lst))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options)))
  (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                          (type-options-p options)
                          (good-typed-term-list-p tterm-lst options)
                          (typed-term-list-consp tterm-lst))))
        (make-typed-term))
       ((typed-term-list ttl) tterm-lst)
       ((cons lst-hd &) ttl.term-lst)
       ((mv err judge-hd)
        (case-match ttl.judgements
          ((& judge-hd & &)
           (mv nil judge-hd))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-list->car
            "Malformed fncall judgements ~q0" ttl.judgements)))
    (make-typed-term :term lst-hd
                     :path-cond ttl.path-cond
                     :judgements judge-hd)))

(define typed-term-list->cdr ((tterm-lst typed-term-list-p)
                              (options type-options-p))
  :guard (and (good-typed-term-list-p tterm-lst options)
              (typed-term-list-consp tterm-lst))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl options)))
  (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                          (type-options-p options)
                          (good-typed-term-list-p tterm-lst options)
                          (typed-term-list-consp tterm-lst))))
        (make-typed-term-list))
       ((typed-term-list ttl) tterm-lst)
       ((cons & lst-tl) ttl.term-lst)
       ((mv err judge-tl)
        (case-match ttl.judgements
          ((& & judge-tl &)
           (mv nil judge-tl))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-list->cdr
            "Malformed fncall judgements ~q0" ttl.judgements)))
    (make-typed-term-list :term-lst lst-tl
                          :path-cond ttl.path-cond
                          :judgements judge-tl))
  ///
  (more-returns
   (new-ttl (implies (and (typed-term-list-p tterm-lst)
                          (type-options-p options)
                          (good-typed-term-list-p tterm-lst options)
                          (typed-term-list-consp tterm-lst))
                     (< (acl2-count (typed-term-list->term-lst new-ttl))
                        (acl2-count (typed-term-list->term-lst tterm-lst))))
            :name acl2-count-of-typed-term-list->cdr)))

;; -----------------------------------------------
;; Theorems for constructors
(defthm implies-of-good-typed-term
  (implies (and (typed-term-p tterm)
                (typed-term-list-p tterm-lst)
                (type-options-p options)
                (good-typed-term-p tterm options)
                (good-typed-term-list-p tterm-lst options)
                (equal (typed-term->path-cond tterm)
                       (typed-term-list->path-cond tterm-lst)))
           (good-typed-term-list-p
            (typed-term-list (cons (typed-term->term tterm)
                                   (typed-term-list->term-lst tterm-lst))
                             (typed-term->path-cond tterm)
                             (list* 'if
                                    (typed-term->judgements tterm)
                                    (typed-term-list->judgements tterm-lst)
                                    '('nil)))
            options))
  :hints (("Goal"
           :expand (good-typed-term-list-p
                    (typed-term-list (cons (typed-term->term tterm)
                                           (typed-term-list->term-lst tterm-lst))
                                     (typed-term->path-cond tterm)
                                     (list* 'if
                                            (typed-term->judgements tterm)
                                            (typed-term-list->judgements tterm-lst)
                                            '('nil)))
                    options))))

;; --------------------------------------------------------------------
;;      Constructors

;; (define typed-term-if->cons ((tt-cond typed-term-p)
;;                              (tt-then typed-term-p)
;;                              (tt-else typed-term-p))
;;   :guard (and (good-typed-term-p tt-cond)
;;               (good-typed-term-p tt-then)
;;               (good-typed-term-p tt-else))
;;   :returns (new-tt (and (typed-term-p new-tt)
;;                         (good-typed-term-p new-tt)))
;;   (b* (((unless (mbt (and (typed-term-p tt-cond)
;;                           (typed-term-p tt-then)
;;                           (typed-term-p tt-else)
;;                           (good-typed-term-p tt-cond)
;;                           (good-typed-term-p tt-then)
;;                           (good-typed-term-p tt-else))))
;;         (make-typed-term))
;;        ((typed-term ttc) tt-cond)
;;        ((typed-term ttt) tt-then)
;;        ((typed-term tte) tt-else)
;;        )
;;     ())
;;   )

(define typed-term-list->cons ((tterm typed-term-p)
                               (tterm-lst typed-term-list-p)
                               (options type-options-p))
  :guard (and (good-typed-term-p tterm options)
              (good-typed-term-list-p tterm-lst options))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (typed-term-list-p tterm-lst)
                          (type-options-p options)
                          (good-typed-term-p tterm options)
                          (good-typed-term-list-p tterm-lst options))))
        (make-typed-term-list))
       ((typed-term tt) tterm)
       ((typed-term-list ttl) tterm-lst)
       ((unless (equal tt.path-cond ttl.path-cond))
        (prog2$
         (er hard? 'typed-term=>typed-term-list->cons
             "Path condition for head and tail of typed-term-list->cons is not ~
              the same: ~p0 ~p1~%" tt.path-cond ttl.path-cond)
         (make-typed-term-list))))
    (make-typed-term-list :term-lst `(,tt.term ,@ttl.term-lst)
                          :path-cond tt.path-cond
                          :judgements `(if ,tt.judgements ,ttl.judgements 'nil))))
