;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "config")

;; verified
(include-book "verified/basics")
(include-book "verified/computed-hints")
(include-book "verified/extractor")
(include-book "verified/process")
(include-book "verified/hint-interface")
(include-book "verified/hint-please")
(include-book "verified/type-hyp")
(include-book "verified/add-hypo-cp")
(include-book "verified/expand-cp")
(include-book "verified/type-extract-cp")
(include-book "verified/uninterpreted-fn-cp")

;; trusted
(include-book "trusted/prove")
(include-book "trusted/run")
(include-book "trusted/trusted-cp")
(include-book "trusted/write")

;; trusted/z3-py
(include-book "trusted/z3-py/header")
(include-book "trusted/z3-py/names")
(include-book "trusted/z3-py/translator")
(include-book "trusted/z3-py/magic-fix")

(in-theory (disable consp-when-member-equal-of-sym-nat-alistp
                    symbol-listp-of-formals-of-pseudo-lambdap
                    consp-of-pseudo-lambdap
                    consp-of-cddr-of-pseudo-lambdap
                    not-stringp-of-cadr-of-pseudo-lambdap))
