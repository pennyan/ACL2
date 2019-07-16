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
(include-book "../../utils/basics")

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

(local
 (defthm symbol-listp-of-strip-cdrs-of-symbol-symbol-alistp
   (implies (symbol-symbol-alistp x)
            (symbol-listp (strip-cdrs x)))
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
                                          (hypo pseudo-term-listp)
                                          (precond pseudo-term-list-listp))
  :returns (term pseudo-term-list-listp)
  (b* ((rec (symbol-fix rec))
       (precond (pseudo-term-list-list-fix precond))
       (constructor (symbol-fix constructor))
       (hypo (pseudo-term-list-fix hypo))
       ((if (or (equal constructor 'quote) (equal rec 'quote)))
        (er hard? 'fixtype-precond-template=>precond-prod-type-of-constructor
            "A constructor named 'quote?~%"))
       (destructor-alst (symbol-symbol-alist-fix destructor-alst))
       (var-lst (strip-cdrs destructor-alst)))
    (cons `(,@hypo
            (,rec (,constructor ,@var-lst)))
          precond)))

(define precond-prod-type-of-destructor-list ((rec symbolp)
                                              (destructor-alst
                                               symbol-symbol-alistp)
                                              (precond pseudo-term-list-listp))
  :returns (term pseudo-term-list-listp)
  :measure (len destructor-alst)
  :hints (("Goal"
           :in-theory (enable symbol-symbol-alist-fix)))
  (b* ((rec (symbol-fix rec))
       (precond (pseudo-term-list-list-fix precond))
       (destructor-alst (symbol-symbol-alist-fix destructor-alst))
       ((if (equal rec 'quote))
        (er hard? 'fixtype-precond-template=>precond-prod-type-of-constructor
            "A constructor named 'quote?~%"))
       ((unless (consp destructor-alst)) precond)
       ((cons (cons type destructor) rest) destructor-alst)
       (first-precond `((not (,rec x))
                        (,type (,destructor x)))))
    (precond-prod-type-of-destructor-list rec rest
                                          (cons first-precond precond))))

(define precond-prod-destructor-of-constructors ((rec symbolp)
                                                 (constructor symbolp)
                                                 (hypo pseudo-term-listp)
                                                 (var-lst symbol-listp)
                                                 (var-lst-total symbol-listp)
                                                 (precond pseudo-term-list-listp))
  :returns (term pseudo-term-list-listp)
  :measure (len var-lst)
  (b* ((rec (symbol-fix rec))
       (precond (pseudo-term-list-list-fix precond))
       (constructor (symbol-fix constructor))
       (var-lst (symbol-list-fix var-lst))
       ((if (or (equal constructor 'quote) (equal rec 'quote)))
        (er hard? 'fixtype-precond-template=>precond-prod-type-of-constructor
            "A constructor named 'quote?~%"))
       (hypo (pseudo-term-list-fix hypo))
       ((unless (consp var-lst)) precond)
       ((cons first-var rest-var) var-lst)
       (first-precond `(,@hypo
                        (equal (,first-var (,constructor ,@var-lst-total))
                               ,first-var))))
    (precond-prod-destructor-of-constructors rec constructor hypo
                                             rest-var var-lst-total
                                             (cons first-precond precond))))

(define precond-destructor-alist ((destructors type-function-list-p))
  :returns (destructor-alst symbol-symbol-alistp)
  :measure (len destructors)
  (b* ((destructors (type-function-list-fix destructors))
       ((unless (consp destructors)) nil)
       ((cons first rest) destructors)
       ((type-function f) first)
       (return-type (type-function->return-type f)))
    (acons return-type f.name (precond-destructor-alist rest))))

(define precond-prod ((prod prod-p)
                      (precond pseudo-term-list-listp))
  :returns (term pseudo-term-list-listp)
  (b* ((prod (prod-fix prod))
       (precond (pseudo-term-list-list-fix precond))
       ((prod p) prod)
       (constructor (type-function->name p.constructor))
       (rec (type-function->return-type p.constructor))
       (destructor-alst (precond-destructor-alist p.destructors))
       (hypo (precond-type-list destructor-alst))
       (type-of-constructor
        (precond-prod-type-of-constructor rec constructor destructor-alst
                                          hypo precond))
       (type-of-destructors
        (precond-prod-type-of-destructor-list rec destructor-alst
                                              type-of-constructor))
       (var-lst (strip-cdrs destructor-alst))
       (destructor-of-constructors
        (precond-prod-destructor-of-constructors rec constructor hypo
                                                 var-lst var-lst
                                                 type-of-destructors))
       (- (cw "preconds: ~q0" destructor-of-constructors)))
    destructor-of-constructors))
