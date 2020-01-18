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

(include-book "../utils/basics")
(include-book "path-cond")
(include-book "evaluator")

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
    ((term pseudo-termp)
     (path-cond pseudo-termp)
     (judgements pseudo-termp)))

  (defprod typed-term-list
    ((term-lst pseudo-term-listp)
     (path-cond pseudo-termp)
     (judgements pseudo-termp)))
  )

;; ---------------------------------------------
;;       Recognizers

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

(define good-typed-lambda-p ((tterm typed-term-p))
  :returns (ok booleanp)
  :guard (and (consp (typed-term->term tterm))
              (pseudo-lambdap (car (typed-term->term tterm))))
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
       ((cons fn actuals) tt.term)
       (formals (lambda-formals fn))
       (body (lambda-body fn))
       ((unless (consp tt.judgements)) nil)
       (match?
        (case-match tt.judgements
          (('if return-judge
               ('if (('lambda !formals body-judge))
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
  (b* ((tterm (pseudo-term-fix tterm))
       ((typed-term tt) tterm)
       ((list & cond then else) tt.term)
       ((unless (consp tt.judgements)) nil)
       (match?
        (case-match tt.judgements
          (('if judge-if-top
               ('if judge-cond
                   ('if !cond judge-then judge-else))
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
              (symbolp (car (typed-term->term tterm))))
  (b* ((tterm (pseudo-term-fix tterm))
       ((typed-term tt) tterm)
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
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
       ((if (acl2::variablep tt.term)) (good-typed-variable-p tt))
       ((if (acl2::quotep tt.term)) (good-typed-quote-p tt))
       ((cons fn &) tt.term)
       ((if (pseudo-lambdap fn)) (good-typed-lambda-p tt))
       ((if (equal fn 'if)) (good-typed-if-p tt)))
    (good-typed-fncall-p tt)))

(define good-typed-term-list-p ((tterm-lst typed-term-list-p))
  :returns (ok booleanp)
  (b* ((tterm-lst (typed-term-list-fix tterm-lst))
       ((typed-term-list ttl) tterm-lst)
       ((unless (is-conjunct? ttl.judgements))
        (er hard? 'typed-term=>good-typed-term-list-p
            "Judgements ~p0 is not a conjunct.~%" ttl.judgements))
       ((if (and (null ttl.term-lst) (equal ttl.judgements ''t))) t)
       ((if (null ttl.term-lst))
        (er hard? 'typed-term=>good-typed-term-list-p
            "Term runs out but there are judgements left ~p0.~%"
            ttl.judgements))
       ((if (equal ttl.judgements ''t))
        (er hard? 'typed-term=>good-typed-term-list-p
            "Judgements runs out but there are terms left ~p0.~%"
            ttl.term-lst))
       ((cons term-hd term-tl) ttl.term-lst)
       ((list & judge-hd judge-tl &) ttl.judgements))
    (and (good-typed-term-p
          (make-typed-term :term term-hd
                           :path-cond ttl.path-cond
                           :judgements judge-hd))
         (good-typed-term-list-p
          (make-typed-term :term term-tl
                           :path-cond ttl.path-cond
                           :judgements judge-tl)))))
)

stop
;; ---------------------------------------------
;;       Destructors for judgements

(define typed-term->kind-consistency ((tterm typed-term-p)
                                      (kind symbolp))
  :returns (kind symbolp)
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
       (check? (case-match kind
                 ('variablep (variable-judgements-p tt.judgements))
                 ('quotep (quote-judgements-p tt.judgements))
                 ('lambdap (lambda-judgements-p tt.judgements))
                 ('ifp (if-judgements-p tt.judgements))
                 ('fncallp (fncall-judgements-p tt.judgements))
                 (& nil)))
       ((unless check?)
        (er hard? 'type-inference-topdown=>typed-term->kind-consistency
            "Term ~p0 is variablep, but judgements ~p1 is not ~
               variable-judgements-p.~%" tt.term tt.judgements)))
    kind))

(define typed-term->kind ((tterm typed-term-p))
  :returns (kind symbolp)
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
       ((if (acl2::variablep tt.term))
        (typed-term->kind-consistency tt 'variablep))
       ((if (acl2::quotep tt.term))
        (typed-term->kind-consistency tt 'quotep))
       ((cons fn &) tt.term)
       ((if (pseudo-lambdap fn))
        (typed-term->kind-consistency tt 'lambdap))
       ((if (equal fn 'if))
        (typed-term->kind-consistency tt 'ifp)))
    (typed-term->kind-consistency tt 'fncallp))
  ///
  (more-returns
   (kind (member-equal kind '(variablep quotep lambdap ifp fncallp nil))
         :name range-of-typed-term->kind)
   (kind (implies (equal kind 'variablep)
                  (acl2::variablep (typed-term->term tterm)))
         :name implies-of-variable-kind)
   (kind (implies (equal kind 'quotep)
                  (acl2::quotep (typed-term->term tterm)))
         :name implies-of-quote-kind)
   (kind (implies (equal kind 'lambdap)
                  (pseudo-lambdap (car (typed-term->term tterm))))
         :name implies-of-lambda-kind)
   (kind (implies (equal kind 'ifp)
                  (equal (car (typed-term->term tterm)) 'if))
         :name implies-of-if-kind)
   (kind (implies (equal kind 'fncallp)
                  (and (not (equal (car (typed-term->term tterm)) 'quote))
                       (symbolp (car (typed-term->term tterm)))))
         :name implies-of-fncall-kind)))

;; ------------------------------------------------
;;       destructors

;; ifp destructors
(local (in-theory (disable len)))

(define typed-term-ifp->cond ((tterm typed-term-p))
  :guard (equal (typed-term->kind tterm) 'ifp)
  :guard-hints (("Goal" :in-theory (enable len)))
  :returns (cond-tt typed-term-p)
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
       ((unless (mbt (equal (typed-term->kind tt) 'ifp)))
        (make-typed-term))
       ((unless (equal (len tt.term) 4))
        (prog2$ (er hard? 'type-inference-topdown=>typed-term-ifp->cond
                    "If statement is malformed: ~q0" tt.term)
                (make-typed-term)))
       (cond-term (cadr tt.term))
       (cond-path-cond tt.path-cond)
       ((mv err cond-judgements)
        (case-match tt.judgements
          (('if & ('if judge-cond & &) &)
           (mv nil judge-cond))
          (& (mv t nil))))
       ((if err)
        (er hard? 'type-inference-topdown=>typed-term-ifp->cond
            "If judgements is malformed: ~q0" tt.judgements)))
    (make-typed-term :term cond-term
                     :path-cond cond-path-cond
                     :judgements cond-judgements)))

;; lambdap destructors
(define typed-term-lambdap->)

;; fncallp destructors
(define typed-term-fncallp->)
