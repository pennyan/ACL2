;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 25th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;
(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "pseudo-lambda-lemmas")

;; easy-fix is a macro for defining a fty::deffixtype when we've got a
;;   recognizer function and a default value.
(defun easy-fix-fn (type-name default-value)
  (b* ((type-str (symbol-name type-name))
       (type-pred (intern-in-package-of-symbol (concatenate 'string type-str "-P") type-name))
       (type-fix (intern-in-package-of-symbol (concatenate 'string type-str "-FIX") type-name))
       (type-fix-lemma (intern-in-package-of-symbol (concatenate 'string type-str "-FIX-WHEN-" type-str "-P") type-name))
       (type-equiv (intern-in-package-of-symbol (concatenate 'string type-str "-EQUIV") type-name)))
    `(defsection ,type-name
       (define ,type-fix ((x ,type-pred))
         :returns(fix-x ,type-pred)
         (mbe :logic (if (,type-pred x) x ,default-value)
              :exec  x)
         ///
         (more-returns
          (fix-x (implies (,type-pred x) (equal fix-x x))
                 :hints(("Goal" :in-theory (enable ,type-fix)))
                 :name ,type-fix-lemma)))
       (deffixtype ,type-name
         :pred   ,type-pred
         :fix    ,type-fix
         :equiv  ,type-equiv
         :define t
         :topic  ,type-name))))

(defmacro easy-fix (type-name default-value)
  `(make-event (easy-fix-fn ',type-name ',default-value)))

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

(defthm pseudo-term-listp-of-symbol-listp
  (implies (symbol-listp x) (pseudo-term-listp x)))

(defthm pseudo-termp-of-fncall
  (implies (and (symbolp fn) (pseudo-termp x))
           (pseudo-termp (list fn x)))
  :hints (("Goal" :in-theory (enable pseudo-termp
                                     pseudo-term-listp))))

(defthm symbolp-of-fn-call-of-pseudo-termp
  (implies (and (pseudo-termp x)
                (consp x)
                (not (acl2::fquotep x))
                (not (pseudo-lambdap (car x))))
           (symbolp (car x)))
  :hints (("Goal" :in-theory (enable pseudo-lambdap))))

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

(defthmd pseudo-term-listp-of-cdr-pseudo-termp
  (implies (and (pseudo-termp term)
                (consp term)
                (not (equal (car term) 'quote)))
           (pseudo-term-listp (cdr term)))
  :hints (("Goal" :in-theory (enable pseudo-termp))))

(defthmd pseudo-termp-of-car-of-pseudo-term-listp
  (implies (and (pseudo-term-listp term)
                (consp term))
           (pseudo-termp (car term))))

(defthm pseudo-term-listp-of-cdr-of-pseudo-termp
  (implies (and (pseudo-termp term)
                (consp term)
                (pseudo-lambdap (car term)))
           (and (true-listp (cdr term))
                (pseudo-term-listp (cdr term)))))

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

(defthm pseudo-term-alistp-of-pairlis$-of-symbol-listp-and-pseudo-term-listp
  (implies (and (symbol-listp y)
                (pseudo-term-listp x))
           (pseudo-term-alistp (pairlis$ y x))))

(defthm nil-of-assoc-equal-of-pseudo-term-alistp
  (implies (and (pseudo-term-alistp x) (not (consp (assoc-equal y x))))
           (not (assoc-equal y x))))

(define true-list-fix ((lst true-listp))
  :parents (SMT-hint-interface)
  :short "Fixing function for true-listp."
  :returns (fixed-lst true-listp)
  (mbe :logic (if (consp lst)
                  (cons (car lst)
                        (true-list-fix (cdr lst)))
                nil)
       :exec lst))

(defthm true-list-fix-idempotent-lemma
  (equal (true-list-fix (true-list-fix x))
         (true-list-fix x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm true-list-fix-preserve-length
  (equal (len (true-list-fix x))
         (len x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm true-list-fix-when-true-listp
  (implies (true-listp x)
           (equal (true-list-fix x) x))
  :hints (("Goal" :in-theory (enable true-listp true-list-fix))))

(deffixtype true-list
  :fix true-list-fix
  :pred true-listp
  :equiv true-list-equiv
  :define t
  :forward t
  :topic true-listp)

(defalist symbol-symbol-alist
  :key-type symbolp
  :val-type symbolp
  :pred symbol-symbol-alistp
  :true-listp t)

(defthm cdr-of-symbol-symbol-alistp
  (implies (symbol-symbol-alistp x)
           (symbol-symbol-alistp (cdr x))))

(deflist symbol-list-list
  :elt-type symbol-listp
  :pred symbol-list-listp
  :true-listp t)

(defalist scope
  :key-type symbol-listp
  :val-type pseudo-term-listp
  :true-listp t)

