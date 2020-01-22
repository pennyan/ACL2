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

(include-book "type-options")

(define only-one-var-acc ((term-lst pseudo-term-listp)
                          (term pseudo-termp)
                          (count natp))
  :returns (ok booleanp)
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       (count (nfix count))
       ((unless (consp term-lst)) (equal count 1))
       ((cons first rest) term-lst)
       ((if (equal first term))
        (only-one-var-acc rest term (1+ count)))
       ((if (acl2::variablep first)) nil)
       ((if (acl2::fquotep first))
        (only-one-var-acc rest term count)))
    nil))

(define only-one-var ((term-lst pseudo-term-listp)
                      (term pseudo-termp))
  :returns (ok booleanp)
  (only-one-var-acc term-lst term 0))

(define type-predicate-p ((judge pseudo-termp)
                          (supertype-alst type-to-types-alist-p))
  :returns (ok booleanp)
  (and (pseudo-termp judge)
       (equal (len judge) 2)
       (symbolp (car judge))
       (not (equal (car judge) 'quote))
       (is-type? (car judge) supertype-alst))
  ///
  (more-returns
   (ok (implies ok
                (and (consp judge)
                     (symbolp (car judge))
                     (pseudo-termp (cadr judge))))
       :name implies-of-type-predicate-p)))

(define type-predicate-of-term ((judge pseudo-termp)
                                (term pseudo-termp)
                                (supertype-alst type-to-types-alist-p))
  :returns (ok booleanp)
  (and (pseudo-termp judge)
       (equal (len judge) 2)
       (symbolp (car judge))
       (not (equal (car judge) 'quote))
       (is-type? (car judge) supertype-alst)
       (equal term (cadr judge))))

(define single-var-fncall-of-term ((judge pseudo-termp)
                                   (term pseudo-termp))
  :returns (ok booleanp)
  (and (pseudo-termp judge)
       (consp judge)
       (symbolp (car judge))
       (not (equal (car judge) 'quote))
       (only-one-var (cdr judge) term)))

(define judgement-of-term ((judge pseudo-termp)
                           (term pseudo-termp)
                           (supertype-alst type-to-types-alist-p))
  :returns (ok booleanp)
  (or (equal judge term)
      (type-predicate-of-term judge term supertype-alst)
      (single-var-fncall-of-term judge term)))

#|
(judgement-of-term '(rationalp r1)
                   'r1
                   '((integerp . rationalp)))

(judgement-of-term '(< r1 '0)
                   'r1
                   '((integerp . rationalp)))

(judgement-of-term '(< r1 r2)
                   'r1
                   '((integerp . rationalp)))
|#

(define is-conjunct? ((term pseudo-termp))
  :returns (ok booleanp)
  (b* ((term (pseudo-term-fix term)))
    (implies (not (equal term ''t))
             (and (consp term)
                  (equal (car term) 'if)
                  (equal (len term) 4)
                  (equal (cadddr term) ''nil))))
  ///
  (more-returns
   (ok (implies (and ok (pseudo-termp term) (not (equal term ''t)))
                (and (consp term)
                     (equal (len term) 4)
                     (pseudo-termp (cadr term))
                     (pseudo-termp (caddr term))))
       :name implies-of-is-conjunct?)
   (ok (implies (and ok (pseudo-termp term) (not (equal term ''t)))
                (< (acl2-count (caddr term))
                   (acl2-count term)))
       :name acl2-count-of-caddr-of-is-conjunct?
       :hints (("Goal"
                :in-theory (disable implies-of-is-conjunct?
                                    symbol-listp)))
       :rule-classes :linear)))

(defthm is-conjunct?-unbearable
  (implies (and (pseudo-termp actuals-judgements)
                (not (equal actuals-judgements ''t))
                (is-conjunct? actuals-judgements))
           (and (consp (cdr actuals-judgements))
                (consp (cddr actuals-judgements))))
  :hints (("Goal"
           :in-theory (enable is-conjunct?))))

(defthm is-conjunct?-constructor
  (implies (and (pseudo-termp first)
                (pseudo-termp rest))
           (is-conjunct? `(if ,first ,rest 'nil)))
  :hints (("Goal"
           :in-theory (enable is-conjunct?))))

(define is-conjunct-list? ((term pseudo-termp))
  :returns (ok booleanp)
  :measure (acl2-count (pseudo-term-fix term))
  (b* ((term (pseudo-term-fix term))
       ((unless (is-conjunct? term)) nil)
       ((if (equal term ''t)) t)
       ((list & & then &) term))
    (is-conjunct-list? then)))
