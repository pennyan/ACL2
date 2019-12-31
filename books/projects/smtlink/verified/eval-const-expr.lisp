;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
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

(define not-free? ((expr pseudo-termp))
  :returns (ok booleanp)
  (null (acl2::all-vars expr)))

(defines eval-const-expr

(define eval-const-expr ((expr pseudo-termp))
  :returns (val any-p)
  (b* ((expr (pseudo-term-fix expr))
       (not-free? (not-free? expr))
       ((unless not-free?)
        (er hard? 'type-inference=>eval-const-expr
            "Expression ~p0 is not a constant expression. Therefore, abort ~
             evaluation.~%" expr))
       
       )
    ()))

(define eval-const-expr-list ((expr-list pseudo-term-listp))
  (b* ((expr-list (pseudo-term-list-fix expr-list))
       ((unless (consp expr-list)) nil)
       ((cons hd tl) expr-list))
    (cons (eval-const-expr hd)
          (eval-const-expr-list tl))))
)
