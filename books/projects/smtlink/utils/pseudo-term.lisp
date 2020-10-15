;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(defthm true-list-fix-preserve-length
  (equal (len (acl2::true-list-fix x))
         (len x))
  :hints (("Goal" :in-theory (enable acl2::true-list-fix))))

(define pseudo-term-fix ((x pseudo-termp))
  :returns (fixed pseudo-termp)
  (mbe :logic (if (pseudo-termp x) x nil)
       :exec x)
  ///
  (more-returns
   (fixed (implies (pseudo-termp x) (equal fixed x))
          :name equal-fixed-and-x-of-pseudo-termp)))

(defthm pseudo-term-fix-idempotent-lemma
  (equal (pseudo-term-fix (pseudo-term-fix x))
         (pseudo-term-fix x))
  :hints (("Goal" :in-theory (enable pseudo-term-fix))))

(deffixtype pseudo-term
  :fix pseudo-term-fix
  :pred pseudo-termp
  :equiv pseudo-term-equiv
  :define t
  :forward t
  :topic pseudo-termp)

(define pseudo-term-list-fix ((x pseudo-term-listp))
  :returns (new-x pseudo-term-listp)
  (mbe :logic (if (consp x)
                  (cons (pseudo-term-fix (car x))
                        (pseudo-term-list-fix (cdr x)))
                nil)
       :exec x)
  ///
  (more-returns
   (new-x (<= (acl2-count new-x) (acl2-count x))
          :name acl2-count-<=-pseudo-term-list-fix
          :rule-classes :linear
          :hints (("Goal" :in-theory (enable pseudo-term-fix))))
   (new-x (implies (pseudo-term-listp x)
                   (equal new-x x))
          :name equal-pseudo-term-list-fix)
   (new-x (implies (pseudo-term-listp x)
                   (equal (len new-x) (len x)))
          :name len-equal-pseudo-term-list-fix
          :rule-classes :linear)))

(defthm pseudo-term-list-fix-idempotent-lemma
  (equal (pseudo-term-list-fix (pseudo-term-list-fix x))
         (pseudo-term-list-fix x))
  :hints (("Goal" :in-theory (enable pseudo-term-list-fix))))

(deffixtype pseudo-term-list
  :fix pseudo-term-list-fix
  :pred pseudo-term-listp
  :equiv pseudo-term-list-equiv
  :define t)

(define pseudo-term-list-list-fix ((x pseudo-term-list-listp))
  :returns (fixed pseudo-term-list-listp)
  (mbe :logic (if (consp x)
                  (cons (pseudo-term-list-fix (car x))
                        (pseudo-term-list-list-fix (cdr x)))
                nil)
       :exec x))

(defthm pseudo-term-list-list-fix-idempotent-lemma
  (equal (pseudo-term-list-list-fix (pseudo-term-list-list-fix x))
         (pseudo-term-list-list-fix x))
  :hints (("Goal" :in-theory (enable pseudo-term-list-list-fix))))

(deffixtype pseudo-term-list-list
  :fix pseudo-term-list-list-fix
  :pred pseudo-term-list-listp
  :equiv pseudo-term-list-list-equiv
  :define t
  :forward t
  :topic pseudo-term-list-listp)

(defalist pseudo-term-alist
  :key-type pseudo-term
  :val-type pseudo-term
  :pred pseudo-term-alistp
  :true-listp t)
