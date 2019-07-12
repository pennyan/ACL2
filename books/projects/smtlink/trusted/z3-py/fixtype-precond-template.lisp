;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (Canada Day, 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "../../verified/fixtypes")

(define precond-array ((rec symbolp)
                       (smt-type smt-type-p)
                       (precond pseudo-term-list-listp))
  :returns (term pseudo-term-list-listp)
  :ignore-ok t
  :irrelevant-formals-ok t
  (pseudo-term-list-list-fix precond))

(local
(defthm pseudo-termp-of-cdar-of-symbol-symbol-alist-fix
  (implies (consp (symbol-symbol-alist-fix x))
           (pseudo-termp (cdr (car (symbol-symbol-alist-fix x)))))
  :hints (("Goal" :in-theory (enable symbol-symbol-alist-fix))))
)

(local
 (defthm pseudo-term-listp-of-strip-cdrs-of-symbol-symbol-alist-fix
   (pseudo-term-listp (strip-cdrs (symbol-symbol-alist-fix x)))
   :hints (("Goal" :in-theory (enable symbol-symbol-alist-fix))))
 )

(define precond-type-list ((destructor-alst symbol-symbol-alistp))
  :returns (term pseudo-term-listp)
  :measure (len destructor-alst)
  :hints (("Goal" :in-theory (enable symbol-symbol-alist-fix)))
  (b* ((destructor-alst (symbol-symbol-alist-fix destructor-alst))
       ((unless (consp destructor-alst)) nil)
       ((cons (cons type var) rest) destructor-alst))
    `((not (,type ,var))
      ,@(precond-type-list rest))))

(local
 (defthm append-of-pseudo-term-listp
   (implies (and (pseudo-term-listp x)
                 (pseudo-term-listp y))
            (pseudo-term-listp (append x y))))
 )

(define precond-prod-type-of-constructor ((rec symbolp)
                                          (constructor symbolp)
                                          (destructor-alst
                                           symbol-symbol-alistp)
                                          (precond pseudo-term-list-listp))
  :returns (term pseudo-term-list-listp)
  (b* ((rec (symbol-fix rec))
       (precond (pseudo-term-list-list-fix precond))
       (constructor (symbol-fix constructor))
       ((if (or (equal constructor 'quote) (equal rec 'quote)))
        (er hard? 'fixtype-precond-template=>precond-prod-type-of-constructor
            "A constructor named 'quote?~%"))
       (destructor-alst (symbol-symbol-alist-fix destructor-alst))
       (var-lst (strip-cdrs destructor-alst)))
    (cons `(,@(precond-type-list destructor-alst)
            (,rec (,constructor ,@var-lst)))
          precond)))

(define precond-prod-type-of-destructor-list ((rec symbolp)
                                              (constructor symbolp)
                                              (destructor-alst
                                               symbol-symbol-alistp)
                                              (precond pseudo-term-list-listp))
  :returns (term pseudo-term-list-listp)
  :ignore-ok t
  :irrelevant-formals-ok t
  (pseudo-term-list-list-fix precond))

(define precond-prod-destructor-of-constructors ((rec symbolp)
                                                 (constructor symbolp)
                                                 (destructor-alst
                                                  symbol-symbol-alistp)
                                                 (precond pseudo-term-list-listp))
  :returns (term pseudo-term-list-listp)
  :ignore-ok t
  :irrelevant-formals-ok t
  (pseudo-term-list-list-fix precond))

(define precond-destructor-alist ((destructors smt-function-list-p)
                                  (fixinfo smt-fixtype-info-p))
  :returns (destructor-alst symbol-symbol-alistp)
  :measure (len destructors)
  (b* ((destructors (smt-function-list-fix destructors))
       ((unless (consp destructors)) nil)
       ((cons first rest) destructors)
       ((smt-function f) first)
       (return-type (return-type-of-function f fixinfo)))
    (acons return-type f.name (precond-destructor-alist rest fixinfo))))

(define precond-prod ((rec symbolp)
                      (prod prod-p)
                      (fixinfo smt-fixtype-info-p)
                      (precond pseudo-term-list-listp))
  :returns (term pseudo-term-list-listp)
  (b* ((rec (symbol-fix rec))
       (prod (prod-fix prod))
       (precond (pseudo-term-list-list-fix precond))
       ((prod p) prod)
       (constructor (smt-function->name p.constructor))
       (destructor-alst (precond-destructor-alist p.destructors fixinfo))
       (type-of-constructor
        (precond-prod-type-of-constructor rec constructor destructor-alst
                                          precond))
       (type-of-destructors
        (precond-prod-type-of-destructor-list rec constructor destructor-alst
                                              type-of-constructor))
       (destructor-of-constructors
        (precond-prod-destructor-of-constructors rec constructor destructor-alst
                                                 type-of-destructors))
       (- (cw "destructor-of-constructors: ~q0" destructor-of-constructors)))
    destructor-of-constructors))
