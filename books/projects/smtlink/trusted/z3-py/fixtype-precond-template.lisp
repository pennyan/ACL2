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

(define precond-array ((name symbolp)
                       (smt-type smt-type-p)
                       (int-to-rat int-to-rat-p)
                       (precond pseudo-term-listp))
  :returns (term pseudo-term-listp)
  :ignore-ok t
  :irrelevant-formals-ok t
  (pseudo-term-list-fix precond))

(define precond-prod ((name symbolp)
                      (prod prod-p)
                      (int-to-rat int-to-rat-p)
                      (precond pseudo-term-listp))
  :returns (term pseudo-term-listp)
  :ignore-ok t
  :irrelevant-formals-ok t
  (pseudo-term-list-fix precond))

(define precond-sum ((name symbolp)
                     (smt-type smt-type-p)
                     (int-to-rat int-to-rat-p)
                     (precond pseudo-term-listp))
  :returns (term pseudo-term-listp)
  :ignore-ok t
  :irrelevant-formals-ok t
  (pseudo-term-list-fix precond))

