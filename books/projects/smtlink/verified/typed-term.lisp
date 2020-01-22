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
    (consp ttl.term-lst)))

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
         :name implies-of-fncall-kind)))

(define good-typed-variable-p ((tterm typed-term-p))
  :returns (ok booleanp)
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
       ((unless (consp tt.judgements)) nil)
       (match?
        (case-match tt.judgements
          (('if judge-set ('if ('if ''t ''t ''nil) ''t ''nil) ''nil)
           (is-conjunct-list? judge-set))
          (& nil))))
    (if match? t nil)))

#|
(good-typed-variable-p (typed-term 'x
                                   ''t
                                   '(if (if (booleanp (rational-integer-alistp x))
                                            't
                                          'nil)
                                        (if (if 't 't 'nil) 't 'nil)
                                      'nil)))
|#

(define good-typed-quote-p ((tterm typed-term-p))
  :returns (ok booleanp)
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
       ((unless (consp tt.judgements)) nil)
       (match? (case-match tt.judgements
                 (('if judge-set ''t ''nil)
                  (is-conjunct-list? judge-set))
                 (& nil))))
    (if match? t nil)))

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

(define good-typed-lambda-p ((tterm typed-term-p))
  :returns (ok booleanp)
  :guard (and (consp (typed-term->term tterm))
              (pseudo-lambdap (car (typed-term->term tterm))))
  :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                 0)
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
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
           (and (is-conjunct-list? return-judge)
                (good-typed-term-list-p
                 (make-typed-term-list :term-lst actuals
                                       :path-cond tt.path-cond
                                       :judgements actuals-judge))
                (b* ((shadowed-path-cond (shadow-path-cond formals tt.path-cond)))
                  (good-typed-term-p
                   (make-typed-term :term body
                                    :path-cond shadowed-path-cond
                                    :judgements body-judge)))))
          (& nil))))
    (if match? t nil)))

(define good-typed-if-p ((tterm typed-term-p))
  :returns (ok booleanp)
  :guard (and (consp (typed-term->term tterm))
              (equal (car (typed-term->term tterm)) 'if))
  :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                 0)
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
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
           (and (is-conjunct? judge-if-top)
                (good-typed-term-p
                 (make-typed-term :term cond
                                  :path-cond tt.path-cond
                                  :judgements judge-cond))
                (good-typed-term-p
                 (make-typed-term :term then
                                  :path-cond
                                  `(if ,(simple-transformer cond)
                                       ,tt.path-cond 'nil)
                                  :judgements judge-then))
                (good-typed-term-p
                 (make-typed-term :term else
                                  :path-cond
                                  `(if ,(simple-transformer `(not ,cond))
                                       ,tt.path-cond 'nil)
                                  :judgements judge-else))))
          (& nil))))
    (if match? t nil)))

(define good-typed-fncall-p ((tterm typed-term-p))
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
           (and (is-conjunct-list? return-judge)
                (good-typed-term-list-p
                 (make-typed-term-list :term-lst actuals
                                       :path-cond tt.path-cond
                                       :judgements actuals-judge))))
          (& nil))))
    (if match? t nil)))

(define good-typed-term-p ((tterm typed-term-p))
  :returns (ok booleanp)
  :measure (list (acl2-count
                  (typed-term->term
                   (typed-term-fix tterm)))
                 1)
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
       ((if (equal (typed-term->kind tt) 'variablep))
        (good-typed-variable-p tt))
       ((if (equal (typed-term->kind tt) 'quotep))
        (good-typed-quote-p tt))
       ((if (equal (typed-term->kind tt) 'lambdap))
        (good-typed-lambda-p tt))
       ((if (equal (typed-term->kind tt) 'ifp))
        (good-typed-if-p tt)))
    (good-typed-fncall-p tt))
  ///
  (more-returns
   (ok (implies (and (typed-term-p tterm) ok
                     (equal (typed-term->kind tterm) 'variablep))
                (good-typed-variable-p tterm))
       :name good-typed-variable-p-of-good-term)
   (ok (implies (and (typed-term-p tterm) ok
                     (equal (typed-term->kind tterm) 'quotep))
                (good-typed-quote-p tterm))
       :name good-typed-quote-p-of-good-term)
   (ok (implies (and (typed-term-p tterm) ok
                     (equal (typed-term->kind tterm) 'lambdap))
                (good-typed-lambda-p tterm))
       :name good-typed-lambda-p-of-good-term)
   (ok (implies (and (typed-term-p tterm) ok
                     (equal (typed-term->kind tterm) 'ifp))
                (good-typed-if-p tterm))
       :name good-typed-if-p-of-good-term)
   (ok (implies (and (typed-term-p tterm) ok
                     (equal (typed-term->kind tterm) 'fncallp))
                (good-typed-fncall-p tterm))
       :name good-typed-fncall-p-of-good-term)))

(define good-typed-term-list-p ((tterm-lst typed-term-list-p))
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
                           :judgements judge-hd))
         (good-typed-term-list-p
          (make-typed-term-list :term-lst term-tl
                                :path-cond ttl.path-cond
                                :judgements judge-tl)))))
)

(local (in-theory (disable pseudo-termp
                           symbol-listp
                           acl2::pseudo-termp-opener
                           pseudo-term-listp-of-symbol-listp)))

(verify-guards good-typed-term-p)

;; -------------------------------------------------------------------
;; Theorems for destructors
;; TODO: simplify the proof

(defthm implies-of-good-typed-if
  (implies (and (typed-term-p tterm) (good-typed-if-p tterm))
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
                             (cadr (caddr (typed-term->judgements tterm)))))
                (good-typed-term-p
                 (typed-term (caddr (typed-term->term tterm))
                             (list* 'if
                                    (simple-transformer (cadr (typed-term->term tterm)))
                                    (typed-term->path-cond tterm)
                                    '('nil))
                             (caddr (caddr (caddr (typed-term->judgements
                                                   tterm))))))
                (good-typed-term-p
                 (typed-term
                  (cadddr (typed-term->term tterm))
                  (list* 'if
                         (simple-transformer (list 'not
                                                   (cadr (typed-term->term tterm))))
                         (typed-term->path-cond tterm)
                         '('nil))
                  (cadddr (caddr (caddr (typed-term->judgements tterm))))))
                (pseudo-termp (caddr (caddr (caddr (typed-term->judgements
                                                    tterm)))))
                (pseudo-termp (cadddr (caddr (caddr (typed-term->judgements
                                                     tterm)))))))
  :hints (("Goal"
           :expand (good-typed-if-p tterm))))

(defthm implies-of-good-typed-fncall
  (implies (and (typed-term-p tterm) (good-typed-fncall-p tterm))
           (and (consp (typed-term->judgements tterm))
                (consp (cdr (typed-term->judgements tterm)))
                (consp (cddr (typed-term->judgements tterm)))
                (pseudo-termp (caddr (typed-term->judgements tterm)))
                (good-typed-term-list-p
                 (typed-term-list (cdr (typed-term->term tterm))
                                  (typed-term->path-cond tterm)
                                  (caddr (typed-term->judgements tterm))))))
  :hints (("Goal"
           :expand (good-typed-fncall-p tterm))))

(defthm implies-of-good-typed-lambda
  (implies (and (typed-term-p tterm) (good-typed-lambda-p tterm))
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
                                                 tterm)))))
                (good-typed-term-p
                 (typed-term (caddr (car (typed-term->term tterm)))
                             (shadow-path-cond (cadr (car (typed-term->term tterm)))
                                               (typed-term->path-cond tterm))
                             (caddr (car (cadr (caddr (typed-term->judgements tterm)))))))))
  :hints (("Goal"
           :expand (good-typed-lambda-p tterm))))

(defthm implies-of-good-typed-term-list
  (implies (and (typed-term-list-p tterm-lst)
                (good-typed-term-list-p tterm-lst)
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
                             (cadr (typed-term-list->judgements tterm-lst))))
                (good-typed-term-list-p
                 (typed-term-list (cdr (typed-term-list->term-lst tterm-lst))
                                  (typed-term-list->path-cond tterm-lst)
                                  (caddr (typed-term-list->judgements
                                          tterm-lst))))))
  :hints (("Goal" :expand ((good-typed-term-list-p tterm-lst)
                           (typed-term-list-consp tterm-lst)))))

;; ---------------------------------------------
;;       Destructors for typed-terms

;; ifp destructors
(define typed-term-ifp->cond ((tterm typed-term-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm))
  :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (equal (typed-term->kind tterm) 'ifp)
                          (good-typed-term-p tterm))))
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

(define typed-term-ifp->then ((tterm typed-term-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm))
  :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (equal (typed-term->kind tterm) 'ifp)
                          (good-typed-term-p tterm))))
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

(define typed-term-ifp->else ((tterm typed-term-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm))
  :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (equal (typed-term->kind tterm) 'ifp)
                          (good-typed-term-p tterm))))
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
(define typed-term-fncallp->actuals ((tterm typed-term-p))
  :guard (and (equal (typed-term->kind tterm) 'fncallp)
              (good-typed-term-p tterm))
  :returns (new-ttl (and (typed-term-list-p new-ttl) (good-typed-term-list-p new-ttl)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (equal (typed-term->kind tterm) 'fncallp)
                          (good-typed-term-p tterm))))
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
(define typed-term-lambdap->actuals ((tterm typed-term-p))
  :guard (and (equal (typed-term->kind tterm) 'lambdap)
              (good-typed-term-p tterm))
  :returns (new-ttl (and (typed-term-list-p new-ttl) (good-typed-term-list-p new-ttl)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (equal (typed-term->kind tterm) 'lambdap)
                          (good-typed-term-p tterm))))
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

(define typed-term-lambdap->body ((tterm typed-term-p))
  :guard (and (equal (typed-term->kind tterm) 'lambdap)
              (good-typed-term-p tterm))
  :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (equal (typed-term->kind tterm) 'lambdap)
                          (good-typed-term-p tterm))))
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
(define typed-term-list->car ((tterm-lst typed-term-list-p))
  :guard (and (good-typed-term-list-p tterm-lst)
              (typed-term-list-consp tterm-lst))
  :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt)))
  (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                          (good-typed-term-list-p tterm-lst)
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

(define typed-term-list->cdr ((tterm-lst typed-term-list-p))
  :guard (and (good-typed-term-list-p tterm-lst)
              (typed-term-list-consp tterm-lst))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl)))
  (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                          (good-typed-term-list-p tterm-lst)
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
                          :judgements judge-tl)))


;; -----------------------------------------------
;; Theorems for constructors
(defthm implies-of-good-typed-term
  (implies (and (typed-term-p tterm)
                (typed-term-list-p tterm-lst)
                (good-typed-term-p tterm)
                (good-typed-term-list-p tterm-lst)
                (equal (typed-term->path-cond tterm)
                       (typed-term-list->path-cond tterm-lst)))
           (good-typed-term-list-p
            (typed-term-list (cons (typed-term->term tterm)
                                   (typed-term-list->term-lst tterm-lst))
                             (typed-term->path-cond tterm)
                             (list* 'if
                                    (typed-term->judgements tterm)
                                    (typed-term-list->judgements tterm-lst)
                                    '('nil)))))
  :hints (("Goal"
           :expand (good-typed-term-list-p
                    (typed-term-list (cons (typed-term->term tterm)
                                           (typed-term-list->term-lst tterm-lst))
                                     (typed-term->path-cond tterm)
                                     (list* 'if
                                            (typed-term->judgements tterm)
                                            (typed-term-list->judgements tterm-lst)
                                            '('nil)))))))

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
                               (tterm-lst typed-term-list-p))
  :guard (and (good-typed-term-p tterm)
              (good-typed-term-list-p tterm-lst))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (typed-term-list-p tterm-lst)
                          (good-typed-term-p tterm)
                          (good-typed-term-list-p tterm-lst))))
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
