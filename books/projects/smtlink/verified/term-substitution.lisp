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

(defines term-substitution
  :well-founded-relation l<
  :verify-guards nil

  (define term-substitution ((term pseudo-termp)
                             (subterm pseudo-termp)
                             (subst pseudo-termp))
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
         ((if (pseudo-lambdap fn))
          (b* ((actuals-substed
                (term-substitution-list actuals subterm subst))
               (formals (lambda-formals fn))
               ((unless (mbt (equal (len formals) (len actuals-substed)))) nil)
               (shadowed? (dumb-occur-vars-or formals subterm))
               ((if shadowed?) `(,fn ,@actuals-substed))
               (body (lambda-body fn))
               (body-substed
                (term-substitution body subterm subst))
               (new-fn `(lambda ,formals ,body-substed)))
            `(,new-fn ,@actuals-substed))))
      `(,fn ,@(term-substitution-list actuals subterm subst))))

  (define term-substitution-list ((term-lst pseudo-term-listp)
                                  (subterm pseudo-termp)
                                  (subst pseudo-termp))
    :returns (substed-term-lst pseudo-term-listp)
    :measure (acl2-count (pseudo-term-list-fix term-lst))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (subterm (pseudo-term-fix subterm))
         (subst (pseudo-term-fix subst))
         ((unless (consp term-lst)) nil)
         ((cons first-term rest-terms) term-lst))
      (cons (term-substitution first-term subterm subst)
            (term-substitution-list rest-terms subterm subst))))
  )

(defthm term-substitution-list-maintain-length
  (implies (and (pseudo-term-listp term-lst)
                (pseudo-termp subterm)
                (pseudo-termp subst))
           (equal (len (term-substitution-list term-lst subterm subst))
                  (len term-lst)))
  :hints (("Goal"
           :in-theory (enable term-substitution term-substitution-list)
           :expand (term-substitution-list term-lst subterm subst))))

(verify-guards term-substitution)
