;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "../config")
(include-book "../utils/basics")

(defsection SMT-hint-interface
  :parents (verified)
  :short "Define default Smtlink hint interface"

  (defprod hint-pair
    :parents (smtlink-hint)
    ((thm pseudo-termp "A theorem statement"
          :default nil)
     (hints true-listp "The ACL2 hint for proving this theorem"
            :default nil)
     (name symbolp "The name of the theorem if already proven in ACL2"
           :default nil)))

  (deflist hint-pair-list
    :parents (hint-pair)
    :elt-type hint-pair
    :true-listp t)

  (defprod decl
    :parents (smtlink-hint)
    ((name symbolp :default nil)
     (type hint-pair-p :default (make-hint-pair))
     ;; The fixer should be found in types;
     ;; So we don't need fixer in function hints.
     ;; (fixer symbolp :default nil)
     ))

  (deflist decl-list
    :parents (decl)
    :elt-type decl
    :true-listp t)

  (defprod smt-function
    :parents (smtlink-hint)
    ((name symbolp :default nil)
     (expansion-depth natp :default 1)
     (formals decl-list-p :default nil)
     (returns decl-list-p :default nil)
     ;; I'm not sure what's good of having guard,
     ;; currently the hint is generated but is not used in Smtlink.
     (guard hint-pair-p :default (make-hint-pair))
     (more-returns hint-pair-list-p :default nil)))

  (defoption maybe-smt-function smt-function-p)

  (deflist smt-function-list
    :parents (smt-function)
    :elt-type smt-function-p
    :true-listp t)

  (defprod prod
    ((kind symbolp :default nil)
     (constructor smt-function-p :default (make-smt-function))
     (field-accessors smt-function-list-p :default nil)
     (theorems hint-pair-list-p :default nil)))

  (deflist prod-list
    :elt-type prod-p
    :true-listp t)

  (defprod option
    ((some-prod prod-p :default (make-prod))
     (none-prod prod-p :default (make-prod))))

  (deftagsum smt-type
    (:abstract ())
    (:list ((cons smt-function-p :default (make-smt-function))
            (car smt-function-p :default (make-smt-function))
            (cdr smt-function-p :default (make-smt-function))
            (empty smt-function-p :default (make-smt-function))
            (elt-type symbolp :default nil)
            (theorems hint-pair-list-p :default nil)))
    (:array ((store smt-function-p :default (make-smt-function))
             (select smt-function-p :default (make-smt-function))
             (key-type symbolp :default nil)
             (val-type symbolp :default nil)
             (theorems hint-pair-list-p :default nil)))
    (:prod ((prod prod-p :default (make-prod))))
    (:option ((option option-p :default (make-option))))
    ;; A prod and an option are all sums,
    ;; we use sum here to denote more general sums
    (:sum ((prods prod-list-p :default nil)))
    )

  (defprod smt-fixtype
    :parents (smtlink-hint)
    ((name symbolp :default nil)
     (recognizer symbolp :default nil)
     (fixer symbolp :default nil)
     (fixer-when-recognizer-thm symbolp :default nil)
     (kind smt-type-p :default (make-smt-type-abstract))))

  (defoption maybe-smt-fixtype smt-fixtype-p)

  (deflist smt-fixtype-list
    :parents (smt-fixtype)
    :elt-type smt-fixtype-p
    :true-listp t)

  (defprod smt-config
    ((smt-cnf smtlink-config-p :default (make-smtlink-config))
     (rm-file booleanp :default t)
     (smt-dir stringp :default "")
     (smt-fname stringp :default "")))

  (deftagsum int-to-rat
    (:switch ((okp booleanp :default nil)))
    (:symbol-list ((lst symbol-listp :default nil))))

  (local (in-theory (disable symbol-listp)))

  (defprod smtlink-hint
    :parents (SMT-hint-interface)
    ((functions smt-function-list-p :default nil)
     (types smt-fixtype-list-p :default nil)
     (hypotheses hint-pair-list-p :default nil)
     (configurations smt-config-p :default (make-smt-config))

     (int-to-rat int-to-rat-p :default (make-int-to-rat-switch :okp nil))
     (use-uninterpreted booleanp :default t)
     (under-induct symbolp :default nil)
     (global-hint symbolp :default nil)
     (wrld-fn-len natp :default 0)
     (custom-p booleanp :default nil)
     ))

  (defalist smtlink-hint-alist
    :key-type symbolp
    :val-type smtlink-hint-p
    :true-listp t)

  (defthm assoc-equal-of-smtlink-hint-alist
    (implies (and (smtlink-hint-alist-p x)
                  (consp (assoc-equal name x)))
             (smtlink-hint-p (cdr (assoc-equal name x)))))
  ;; ---------------------------------------------------------------
  ;; Utility functions

  ;; decl-list functions
  (define get-thm-from-decl ((decl decl-p))
    :returns (thm pseudo-termp)
    (hint-pair->thm (decl->type (decl-fix decl))))

  (define get-thms-from-decl-list ((dlst decl-list-p))
    :returns (thms pseudo-term-listp)
    :measure (len dlst)
    (b* ((dlst (decl-list-fix dlst))
         ((unless (consp dlst)) nil)
         ((cons first rest) dlst))
      (cons (get-thm-from-decl first)
            (get-thms-from-decl-list rest))))

  ;; smt-function-list functions
  (define is-function ((name symbolp) (fn-lst smt-function-list-p))
    :returns (f maybe-smt-function-p)
    :measure (len fn-lst)
    (b* ((fn-lst (smt-function-list-fix fn-lst))
         ((unless (consp fn-lst)) nil)
         ((cons first rest) fn-lst)
         (first-name (smt-function->name first))
         ((if (equal first-name name)) first))
      (is-function name rest)))

  ;; smt-fixtype-list functions
  (define is-type ((x symbolp) (fixtypes smt-fixtype-list-p))
    :returns (type maybe-smt-fixtype-p)
    :measure (len fixtypes)
    (b* ((fixtypes (smt-fixtype-list-fix fixtypes))
         ((unless (consp fixtypes)) nil)
         ((cons first rest) fixtypes)
         ((if (equal x (smt-fixtype->recognizer first))) first))
      (is-type x rest)))

  (define is-recognizer ((x symbolp) (fixtypes smt-fixtype-list-p))
    :returns (okp booleanp)
    :measure (len fixtypes)
    (b* ((fixtypes (smt-fixtype-list-fix fixtypes))
         ((unless (consp fixtypes)) nil)
         ((cons first rest) fixtypes)
         ((if (equal x (smt-fixtype->recognizer first))) t))
      (is-recognizer x rest)))

  (define is-fixer ((x symbolp) (fixtypes smt-fixtype-list-p))
    :returns (okp booleanp)
    :measure (len fixtypes)
    (b* ((fixtypes (smt-fixtype-list-fix fixtypes))
         ((unless (consp fixtypes)) nil)
         ((cons first rest) fixtypes)
         ((if (equal x (smt-fixtype->fixer first))) t))
      (is-fixer x rest)))

  (define name-of-recognizer ((x symbolp) (fixtypes smt-fixtype-list-p))
    :returns (name symbolp)
    :measure (len fixtypes)
    (b* ((fixtypes (smt-fixtype-list-fix fixtypes))
         ((unless (consp fixtypes)) nil)
         ((cons first rest) fixtypes)
         ((if (equal x (smt-fixtype->recognizer first)))
          (smt-fixtype->name first)))
      (name-of-recognizer x rest)))

  (define fncall-of-fixtypes ((x symbolp) (fixtypes smt-fixtype-list-p))
    :returns (ok booleanp)
    :ignore-ok t
    nil)

  (define fixer-of-recognizer ((x symbolp) (fixtypes smt-fixtype-list-p))
    :returns (fixer symbolp)
    :measure (len fixtypes)
    (b* ((fixtypes (smt-fixtype-list-fix fixtypes))
         ((unless (consp fixtypes)) nil)
         ((cons first rest) fixtypes)
         ((if (equal x (smt-fixtype->recognizer first)))
          (smt-fixtype->fixer first)))
      (fixer-of-recognizer x rest)))

  (define recognizer-of-fixer ((x symbolp) (fixtypes smt-fixtype-list-p))
    :returns (recognizer symbolp)
    :measure (len fixtypes)
    (b* ((fixtypes (smt-fixtype-list-fix fixtypes))
         ((unless (consp fixtypes)) nil)
         ((cons first rest) fixtypes)
         ((if (equal x (smt-fixtype->fixer first)))
          (smt-fixtype->recognizer first)))
      (recognizer-of-fixer x rest)))

  (define type-decl-p ((expr pseudo-termp)
                       (fixtypes smt-fixtype-list-p))
    :returns (is-decl? booleanp)
    (b* (;; ((if (is-type-hyp-decl expr)) t)
         ((unless (equal (len expr) 2))
          nil)
         (fn-name (car expr))
         ((unless (symbolp fn-name)) nil)
         ((unless (is-recognizer fn-name fixtypes))
          nil)
         ((unless (and (symbolp (cadr expr)) (cadr expr))) nil))
      t)
    ///
    (more-returns
     (is-decl?
      (implies is-decl?
               (and (consp expr)
                    (consp (cdr expr))
                    (symbolp (car expr))
                    (is-recognizer (car expr) fixtypes)
                    (symbolp (cadr expr)) (cadr expr)))
      :name type-decl-p-definition)))
  )

;; Put a default-hint into smt-hint-table
(table smt-hint-table)

(define get-smt-hint-table ((world plist-worldp))
  (table-alist 'smt-hint-table world))

(defmacro add-smtlink-hint (name hint)
  (declare (xargs :guard (symbolp name)))
  `(table smt-hint-table ',name ,hint))

(add-smtlink-hint :default
                  (make-smtlink-hint
                   :configurations
                   (make-smt-config :smt-cnf (default-smt-cnf))))
