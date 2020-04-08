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
(include-book "term-substitution")

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

  (deflist typed-term-list
    :elt-type typed-term-p
    :true-listp t)

  (define typed-term-list->term-lst ((tterm-lst typed-term-list-p))
    :measure (len (typed-term-list-fix tterm-lst))
    :returns (term-lst pseudo-term-listp)
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((unless (consp tterm-lst)) nil)
         ((cons tterm-hd tterm-tl) tterm-lst)
         ((typed-term tth) tterm-hd))
      (cons tth.term (typed-term-list->term-lst tterm-tl)))
    ///
    (more-returns
     (term-lst
      (equal (acl2-count
              (typed-term-list->term-lst (typed-term-list-fix tterm-lst)))
             (acl2-count term-lst))
      :name acl2-count-equal-of-typed-term-list-fix
      :hints (("Goal"
               :expand (typed-term-list->term-lst tterm-lst))))
     (term-lst
      (implies (consp tterm-lst)
               (< (acl2-count (typed-term->term (car tterm-lst)))
                  (acl2-count term-lst)))
      :name acl2-count-of-car-of-typed-term-list-p)
     (term-lst
      (implies (typed-term-list-p tterm-lst)
               (equal (len term-lst) (len tterm-lst)))
      :name typed-term-list->term-lst-maintains-len)))

  (defthm acl2-count-of-cdr-of-typed-term-list-p
    (implies (consp tterm-lst)
             (< (acl2-count (typed-term-list->term-lst (cdr tterm-lst)))
                (acl2-count (typed-term-list->term-lst tterm-lst))))
    :hints (("Goal"
             :expand (typed-term-list->term-lst tterm-lst))))

  (define typed-term-list->judgements ((tterm-lst typed-term-list-p))
    :measure (len (typed-term-list-fix tterm-lst))
    :returns (judges pseudo-termp)
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((unless (consp tterm-lst)) ''t)
         ((cons tterm-hd tterm-tl) tterm-lst)
         ((typed-term tth) tterm-hd))
      `(if ,tth.judgements
           ,(typed-term-list->judgements tterm-tl)
         'nil)))

  (define uniform-path-cond? ((tterm-lst typed-term-list-p))
    :returns (ok booleanp)
    :measure (len (typed-term-list-fix tterm-lst))
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((unless (consp tterm-lst)) t)
         ((cons tterm-1 tterm-tl) tterm-lst)
         ((unless (consp tterm-tl)) t)
         ((cons tterm-2 &) tterm-tl)
         ((typed-term tt1) tterm-1)
         ((typed-term tt2) tterm-2))
      (and (equal tt1.path-cond tt2.path-cond)
           (uniform-path-cond? tterm-tl)))
    ///
    (more-returns
     (ok (implies (and (typed-term-list-p tterm-lst) ok)
                  (uniform-path-cond? (cdr tterm-lst)))
         :hints (("Goal"
                  :expand (uniform-path-cond? tterm-lst)))
         :name uniform-path-cond?-of-cdr)
     (ok (implies (and (typed-term-list-p tterm-lst)
                       (consp tterm-lst) (consp (cdr tterm-lst))
                       ok)
                  (equal (typed-term->path-cond (cadr tterm-lst))
                         (typed-term->path-cond (car tterm-lst))))
         :hints (("Goal"
                  :expand (uniform-path-cond? tterm-lst)))
         :name equal-of-uniform-path-cond?)))

  (define typed-term-list->path-cond ((tterm-lst typed-term-list-p))
    :returns (path-cond pseudo-termp)
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((unless (uniform-path-cond? tterm-lst)) ''t)
         ((unless (consp tterm-lst)) ''t)
         ((cons tterm-hd &) tterm-lst)
         ((typed-term tth) tterm-hd))
      tth.path-cond)
    ///
    (more-returns
     (path-cond (implies (and (typed-term-list-p tterm-lst)
                              (uniform-path-cond? tterm-lst)
                              (consp tterm-lst))
                         (equal path-cond
                                (typed-term->path-cond (car tterm-lst))))
                :name uniform-path-cond-of-typed-term-list->path-cond)
     (path-cond (implies (and (typed-term-list-p tterm-lst)
                              (not (uniform-path-cond? tterm-lst))
                              (consp tterm-lst))
                         (equal path-cond ''t))
                :hints (("Goal"
                         :expand (uniform-path-cond? tterm-lst)))
                :name not-uniform-path-cond-of-typed-term-list->path-cond)))

  (define make-typed-term-list ((term-lst pseudo-term-listp)
                                (path-cond pseudo-termp)
                                (judges pseudo-termp))
    :returns (tterm-lst typed-term-list-p)
    :measure (len (pseudo-term-list-fix term-lst))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (path-cond (pseudo-term-fix path-cond))
         (judges (pseudo-term-fix judges))
         ((if (and (equal judges ''t) (null term-lst))) nil)
         ((if (or (and (equal judges ''t) (consp term-lst))
                  (and (not (equal judges ''t)) (null term-lst))))
          (er hard? 'typed-term=>make-typed-term-list
              "Term list and judges are not of the same length: ~p0 and ~p1.~%"
              term-lst judges))
         ((unless (is-conjunct? judges))
          (er hard? 'typed-term=>make-typed-term-list
              "Judgements should be a conjunct: ~q0"))
         ((cons term-hd term-tl) term-lst)
         ((list & judge-hd judge-tl &) judges))
      (cons (make-typed-term :term term-hd :path-cond path-cond
                             :judgements judge-hd)
            (make-typed-term-list term-tl path-cond judge-tl)))
    ///
    (defthm acl2-count-of-typed-term-list->term-lst
      (<= (acl2-count
           (typed-term-list->term-lst
            (make-typed-term-list term-lst path-cond judges)))
          (acl2-count term-lst))
      :hints (("Goal"
               :in-theory (enable typed-term-list->term-lst)))
      :rule-classes :linear))
  )
