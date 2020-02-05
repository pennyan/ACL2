;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "../utils/pseudo-term")
(include-book "hint-interface")

(defalist type-to-types-alist
  :key-type symbolp
  :val-type symbol-listp
  :true-listp t)

(defthm assoc-equal-of-type-to-types-alist
  (implies (and (type-to-types-alist-p x)
                (assoc-equal y x))
           (consp (assoc-equal y x))))

(defprod type-tuple
  ((type symbolp)
   (neighbour-type symbolp)))

(defalist type-tuple-to-thm-alist
  :key-type type-tuple-p
  :val-type symbolp
  :true-listp t)

(defthm assoc-equal-of-type-tuple-to-thm-alist
  (implies (and (type-tuple-to-thm-alist-p x)
                (assoc-equal y x))
           (and (consp (assoc-equal y x))
                (symbolp (cdr (assoc-equal y x))))))

(defprod return-spec
  ((formals symbol-listp)
   (return-type symbolp)
   (returns-thm symbolp)))

(deflist return-spec-list
  :elt-type return-spec-p
  :true-listp t)

(fty::deftypes function-description
  (deftagsum arg-decl
    (:next ((next arg-check-p)))
    (:done ((r return-spec-p))))
  (defalist arg-check
    :key-type symbolp
    :val-type arg-decl-p))

(defalist function-description-alist
  :key-type symbolp
  :val-type arg-decl-p
  :true-listp t)

(defthm arg-decl-p-of-assoc-equal-from-function-description-alist-p
  (implies (and (function-description-alist-p y)
                (assoc-equal x y))
           (and (consp (assoc-equal x y))
                (arg-decl-p (cdr (assoc-equal x y))))))

(defprod basic-type-description
  ((recognizer symbolp)
   (fixer symbolp)))

(defalist basic-type-description-alist
  :key-type symbolp
  :val-type basic-type-description-p
  :true-listp t)

(defprod cons-type-description
  ((recognizer symbolp)
   (fixer symbolp)
   (car-type symbolp)
   (cdr-type symbolp)
   (cdr-thm symbolp)))

(defalist cons-type-description-alist
  :key-type symbolp
  :val-type cons-type-description-p
  :true-listp t)

(encapsulate ()
(local (in-theory (disable (:rewrite default-cdr))))
(defprod list-type-description
  ((recognizer symbolp)
   (fixer symbolp)
   (elt-type symbolp)
   (cons-thm symbolp)
   (car-thm symbolp)
   (cdr-thm symbolp)))

(defalist list-type-description-alist
  :key-type symbolp
  :val-type list-type-description-p
  :true-listp t)

(defprod alist-type-description
  ((recognizer symbolp)
   (fixer symbolp)
   (key-type symbolp)
   (val-type symbolp)
   (acons-thm symbolp)
   (assoc-equal-thm symbolp)))

(defalist alist-type-description-alist
  :key-type symbolp
  :val-type alist-type-description-p
  :true-listp t)
)

(encapsulate ()
  (local (in-theory (disable (:rewrite default-cdr)
                             (:rewrite consp-of-pseudo-lambdap)
                             (:rewrite
                              acl2::pseudo-lambdap-of-car-when-pseudo-termp)
                             (:definition pseudo-termp)
                             (:rewrite
                              acl2::true-listp-of-car-when-true-list-listp)
                             (:definition true-list-listp)
                             (:rewrite
                              acl2::true-list-listp-of-cdr-when-true-list-listp)
                             (:definition true-listp)
                             (:definition symbol-listp))))
(defprod prod-type-description
  ((recognizer symbolp)
   (fixer symbolp)
   (field-types symbol-listp)
   (constructor-thm symbolp)
   (destructor-thms symbol-listp)))

(defalist prod-type-description-alist
  :key-type symbolp
  :val-type prod-type-description-p
  :true-listp t)

(defprod option-type-description
  ((recognizer symbolp)
   (fixer symbolp)
   (some-type symbolp)
   (some-constructor-thm symbolp)
   (none-constructor-thm symbolp)
   (some-destructor-thm symbolp)))

(defalist option-type-description-alist
  :key-type symbolp
  :val-type option-type-description-p
  :true-listp t)

(defprod sum-type-description
  ((prod-list prod-type-description-alist-p)))

(defalist sum-type-description-alist
  :key-type symbolp
  :val-type sum-type-description-p
  :true-listp t)

(defprod abstract-type-description
  ((recognizer symbolp)
   (fixer symbolp)))

(defalist abstract-type-description-alist
  :key-type symbolp
  :val-type abstract-type-description-p
  :true-listp t)

(defprod type-options
  ((supertype type-to-types-alist-p)
   (supertype-thm type-tuple-to-thm-alist-p)
   (subtype type-to-types-alist-p)
   (subtype-thm type-tuple-to-thm-alist-p)
   (functions function-description-alist-p)
   (consp cons-type-description-alist-p)
   (basic basic-type-description-alist-p)
   (list list-type-description-alist-p)
   (alist alist-type-description-alist-p)
   (prod prod-type-description-alist-p)
   (option option-type-description-alist-p)
   (sum sum-type-description-alist-p)
   (abstract abstract-type-description-alist-p)))
)

(define is-type? ((type symbolp)
                  (supertype-alst type-to-types-alist-p))
  :returns (ok booleanp)
  (not (null (assoc-equal type (type-to-types-alist-fix supertype-alst)))))

(define construct-type-options ((smtlink-hint smtlink-hint-p))
  :returns (type-options type-options-p)
  :irrelevant-formals-ok t
  :ignore-ok t
  (b* ((smtlink-hint (smtlink-hint-fix smtlink-hint)))
    (make-type-options)))
