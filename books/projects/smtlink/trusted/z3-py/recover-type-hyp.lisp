;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "../../verified/hint-interface")
(include-book "../../verified/basics")

(defsection SMT-recover-types
  :parents (z3-py)
  :short "Recovering types from type-hyp"

  (define recover-type-decl-list ((hyp-lst pseudo-term-listp)
                                  (fixtypes smt-fixtype-list-p))
    :returns (type-decl-list decl-list-p)
    (b* ((fixtypes (smt-fixtype-list-fix fixtypes))
         (hyp-lst (pseudo-term-list-fix hyp-lst))
         ((unless (consp hyp-lst)) nil)
         ((cons first rest) hyp-lst)
         ((unless (type-decl-p first fixtypes))
          (er hard? 'recover-type-hype=>recover-type-decl-list "ill-formed ~
                          type term: ~q0" first))
         (var (cadr first)))
      (cons (make-decl :name var :type (make-hint-pair :thm first))
            (recover-type-decl-list rest fixtypes))))

  (define recover-type-hyp ((decl-list pseudo-term-listp)
                            (fixtypes smt-fixtype-list-p)
                            state)
    ;; :returns (type-decl-list decl-listp)
    :mode :program ;; because of untranslate
    (b* ((decl-list (pseudo-term-list-fix decl-list))
         ((unless (consp decl-list)) nil)
         ((cons first rest) decl-list))
      (case-match first
        (('type-hyp ('hide hyp-lst) tag)
         (cond ((equal tag '':type)
                (b* (;; The reason I need to untranslate is that, a list will
                     ;; be represented as (cons sth (cons sth1 ...)). I don't
                     ;; want to walk through this tree structure.
                     ;; But essentially, :program mode can be avoided if I
                     ;; avoid using untranslate, which means walking through
                     ;; the consed version might be worthwhile.
                     (untranslated-hyp-lst
                      (untranslate hyp-lst nil (w state)))
                     ((unless (and (consp untranslated-hyp-lst)
                                   (equal (car untranslated-hyp-lst) 'list)))
                      (er hard? 'recover-type-hyp=>recover-type-hyp "untranslate ~
                          hyp-lst returns something unrecognizable: ~q0"
                          untranslated-hyp-lst))
                     (hyp-lst (cdr untranslated-hyp-lst))
                     (first-type-decl (recover-type-decl-list hyp-lst fixtypes))
                     (rest-type-decl (recover-type-hyp rest fixtypes state)))
                  (append first-type-decl rest-type-decl)))
               (t (prog2$ (er hard? 'recover-type-hyp=>recover-type-hyp "tag ~
                          isn't recognized: ~q0" tag)
                          nil))))
        (& (prog2$ (er hard? 'recover-type-hyp=>recover-type-hyp
                       "recover-type-hyp found a malformed type-hyp: ~q0"
                       first)
                   nil)))))
  )
