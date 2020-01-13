;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 23rd 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "kestrel/std/system/dumb-occur-var-open" :dir :system)

(include-book "../utils/basics")

(define dumb-occur-vars-or ((var-lst symbol-listp)
                            (term pseudo-termp))
  :returns (occur? booleanp)
  :measure (len var-lst)
  (b* ((var-lst (symbol-list-fix var-lst))
       ((unless (consp var-lst)) nil)
       ((cons first-var rest-vars) var-lst))
    (or (acl2::dumb-occur-var-open first-var term)
        (dumb-occur-vars-or rest-vars term))))

(local
(defthm acl2-count-of-car-of-pseudo-term-list-fix
  (implies (consp (pseudo-term-list-fix term-lst))
           (< (acl2-count (pseudo-term-fix (car (pseudo-term-list-fix term-lst))))
              (acl2-count (pseudo-term-list-fix term-lst))))
  :hints (("Goal" :in-theory (enable pseudo-term-list-fix
                                     pseudo-term-fix))))
)

(local
 (defthm acl2-count-of-cadr-of-pseudo-term-fix
   (implies (equal (len (cdr (pseudo-term-fix term))) 3)
            (< (acl2-count (pseudo-term-fix (cadr (pseudo-term-fix term))))
               (1+ (acl2-count (cdr (pseudo-term-fix term))))))
   :hints (("Goal" :in-theory (enable pseudo-term-fix))))
 )

(local
 (defthm acl2-count-of-caddr-of-pseudo-term-fix
   (implies (equal (len (cdr (pseudo-term-fix term))) 3)
            (< (acl2-count (pseudo-term-fix (caddr (pseudo-term-fix term))))
               (1+ (acl2-count (cdr (pseudo-term-fix term))))))
   :hints (("Goal" :in-theory (enable pseudo-term-fix))))
 )

(local
 (defthm pseudo-term-listp-of-cdddr-symbolp
   (implies (and (equal (len (cdr (pseudo-term-fix term))) 3)
                 (symbolp (car (pseudo-term-fix term))))
            (pseudo-term-listp (cdddr (pseudo-term-fix term))))
   :hints (("Goal" :in-theory (enable pseudo-term-fix pseudo-termp)))))

(defines term-substitution
  :well-founded-relation l<
  :verify-guards nil
  :hints (("Goal" :in-theory (disable len)))

  (define term-substitution ((term pseudo-termp)
                             (subterm pseudo-termp)
                             (subst pseudo-termp)
                             (skip-conj booleanp))
    :returns (substed-term pseudo-termp)
    :short "Substitute subterm in term with subst."
    :measure (acl2-count (pseudo-term-fix term))
    (b* ((term (pseudo-term-fix term))
         (subterm (pseudo-term-fix subterm))
         (subst (pseudo-term-fix subst))
         ((if (equal term subterm)) subst)
         ((if (acl2::variablep term)) term)
         ((if (acl2::fquotep term)) term)
         ((cons fn actuals) term)
         ((if (and skip-conj
                   (equal fn 'if)
                   (equal (len actuals) 3)
                   (equal (cadr actuals) ''t)
                   (equal (caddr actuals) ''nil)))
          `(,fn ,(term-substitution (car actuals) subterm subst skip-conj)
                ,@(cdr actuals)))
         ((if (and skip-conj
                   (equal fn 'if)
                   (equal (len actuals) 3)
                   (equal (caddr actuals) ''nil)))
          `(,fn ,(term-substitution (car actuals) subterm subst skip-conj)
                ,(term-substitution (cadr actuals) subterm subst skip-conj)
                ,(caddr actuals)))
         ((if (pseudo-lambdap fn))
          (b* ((actuals-substed
                (term-substitution-list actuals subterm subst skip-conj))
               (formals (lambda-formals fn))
               ((unless (mbt (equal (len formals) (len actuals-substed)))) nil)
               (shadowed? (dumb-occur-vars-or formals subterm))
               ((if shadowed?) `(,fn ,@actuals-substed))
               (body (lambda-body fn))
               (body-substed
                (term-substitution body subterm subst skip-conj))
               (new-fn `(lambda ,formals ,body-substed)))
            `(,new-fn ,@actuals-substed))))
      `(,fn ,@(term-substitution-list actuals subterm subst skip-conj))))

  (define term-substitution-list ((term-lst pseudo-term-listp)
                                  (subterm pseudo-termp)
                                  (subst pseudo-termp)
                                  (skip-conj booleanp))
    :returns (substed-term-lst pseudo-term-listp)
    :measure (acl2-count (pseudo-term-list-fix term-lst))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (subterm (pseudo-term-fix subterm))
         (subst (pseudo-term-fix subst))
         ((unless (consp term-lst)) nil)
         ((cons first-term rest-terms) term-lst))
      (cons (term-substitution first-term subterm subst skip-conj)
            (term-substitution-list rest-terms subterm subst skip-conj))))
  )

(defthm term-substitution-list-maintain-length
  (implies (and (pseudo-term-listp term-lst)
                (pseudo-termp subterm)
                (pseudo-termp subst))
           (equal (len (term-substitution-list term-lst subterm subst conj))
                  (len term-lst)))
  :hints (("Goal"
           :in-theory (enable term-substitution term-substitution-list)
           :expand (term-substitution-list term-lst subterm subst conj))))

(verify-guards term-substitution)

(define term-substitution-multi ((term pseudo-termp)
                                 (subterm-lst pseudo-term-listp)
                                 (subst-lst pseudo-term-listp)
                                 (skip-conj booleanp))
  :returns (substed-term pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (subterm-lst (pseudo-term-list-fix subterm-lst))
       (subst-lst (pseudo-term-list-fix subst-lst))
       ((unless (and (consp subterm-lst)
                     (consp subst-lst)))
        term)
       ((cons subterm-hd subterm-tl) subterm-lst)
       ((cons subst-hd subst-tl) subst-lst))
    (term-substitution-multi (term-substitution term subterm-hd subst-hd skip-conj)
                             subterm-tl
                             subst-tl
                             skip-conj)))

(define term-substitution-multi-list ((term-lst pseudo-term-listp)
                                      (subterm-lst pseudo-term-listp)
                                      (subst-lst pseudo-term-listp)
                                      (skip-conj booleanp))
  :returns (subted-term-lst pseudo-term-listp)
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       ((unless (consp term-lst)) nil)
       ((cons term-hd term-tl) term-lst))
    (cons (term-substitution-multi term-hd subterm-lst subst-lst skip-conj)
          (term-substitution-multi-list term-tl subterm-lst subst-lst skip-conj))))

