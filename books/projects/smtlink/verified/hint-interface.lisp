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

  (defalist symbol-hint-pair-alist
    :parents (hint-pair)
    :key-type symbolp
    :val-type hint-pair-p
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
     (expansion-depth natp :default 0)
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
     (destructors smt-function-list-p :default nil)
     (theorems symbol-hint-pair-alist-p :default nil)))

  (deflist prod-list
    :elt-type prod-p
    :true-listp t)

  ;; (defprod option
  ;;   ((some-prod prod-p :default (make-prod))
  ;;    (none-prod prod-p :default (make-prod))))

  (deftagsum smt-type
    (:abstract ())
    (:array ((store smt-function-p :default (make-smt-function))
             (select smt-function-p :default (make-smt-function))
             (key-type symbolp :default nil)
             (val-type symbolp :default nil)
             (theorems symbol-hint-pair-alist-p :default nil)))
    ;; prod, list and option are all sums
    (:sum ((prods prod-list-p :default nil)))
    )

  (defprod smt-fixtype
    :parents (smtlink-hint)
    ((name symbolp :default nil)
     (recognizer symbolp :default nil)
     (fixer symbolp :default nil)
     (fixer-when-recognizer-thm hint-pair-p :default (make-hint-pair))
     (basicp symbolp :default nil)
     (kind smt-type-p :default (make-smt-type-abstract))))

  (defoption maybe-smt-fixtype smt-fixtype-p)

  (deflist smt-fixtype-list
    :parents (smt-fixtype)
    :elt-type smt-fixtype-p
    :true-listp t)

  (defprod info-pair
    ((name symbolp)
     (fn-type symbolp))) ;; :store, :select, :recognizer, :fixer, :constructor, :destructor

  (defalist smt-fixtype-info
    :key-type symbolp ;; function name
    :val-type info-pair-p
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
     (types-info smt-fixtype-info-p :default nil)
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
             (and (smtlink-hint-p (cdr (assoc-equal name x)))
                  (cdr (assoc-equal name x)))))
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
  (define generate-info-pair ((fn symbolp)
                              (name symbolp)
                              (fn-type symbolp)
                              (acc smt-fixtype-info-p))
    :returns (info smt-fixtype-info-p)
    (b* ((fn (symbol-fix fn))
         (name (symbol-fix name))
         (fn-type (symbol-fix fn-type))
         (acc (smt-fixtype-info-fix acc)))
      (acons fn
             (make-info-pair :name name
                             :fn-type fn-type)
             acc)))

  (define generate-fixtype-info-array ((name symbolp)
                                       (type smt-type-p)
                                       (acc smt-fixtype-info-p))
    :returns (info smt-fixtype-info-p)
    :guard (equal (smt-type-kind type) :array)
    (b* ((name (symbol-fix name))
         (type (smt-type-fix type))
         (acc (smt-fixtype-info-fix acc))
         ((smt-type-array a) type)
         (store-acc (generate-info-pair (smt-function->name a.store) name :store acc)))
      (generate-info-pair (smt-function->name a.select) name :select store-acc)))

  (define generate-fixtype-info-destructors ((name symbolp)
                                             (destructors smt-function-list-p)
                                             (acc smt-fixtype-info-p))
    :returns (info smt-fixtype-info-p)
    :measure (len destructors)
    (b* ((name (symbol-fix name))
         (destructors (smt-function-list-fix destructors))
         (acc (smt-fixtype-info-fix acc))
         ((unless (consp destructors)) acc)
         ((cons first rest) destructors)
         ((smt-function f) first)
         (first-acc (generate-info-pair f.name name :destructor acc)))
      (generate-fixtype-info-destructors name rest first-acc)))

  (define generate-fixtype-info-prod ((name symbolp)
                                      (prod prod-p)
                                      (acc smt-fixtype-info-p))
    :returns (info smt-fixtype-info-p)
    (b* ((name (symbol-fix name))
         (prod (prod-fix prod))
         ((prod p) prod)
         (acc (smt-fixtype-info-fix acc))
         (constructor-acc
          (generate-info-pair (smt-function->name p.constructor) name :constructor acc)))
      (generate-fixtype-info-destructors name p.destructors constructor-acc)))

  (define generate-fixtype-info-prod-list ((name symbolp)
                                           (prods prod-list-p)
                                           (acc smt-fixtype-info-p))
    :returns (info smt-fixtype-info-p)
    :measure (len prods)
    (b* ((name (symbol-fix name))
         (prods (prod-list-fix prods))
         (acc (smt-fixtype-info-fix acc))
         ((unless (consp prods)) acc)
         ((cons first rest) prods)
         (first-acc (generate-fixtype-info-prod name first acc)))
      (generate-fixtype-info-prod-list name rest first-acc)))

  (define generate-fixtype-info-sum ((name symbolp)
                                     (type smt-type-p)
                                     (acc smt-fixtype-info-p))
    :returns (info smt-fixtype-info-p)
    :guard (equal (smt-type-kind type) :sum)
    (b* ((type (smt-type-fix type))
         (acc (smt-fixtype-info-fix acc))
         ((smt-type-sum s) type))
      (generate-fixtype-info-prod-list name s.prods acc)))

  (define generate-fixtype-info-kind ((name symbolp)
                                      (type smt-type-p)
                                      (acc smt-fixtype-info-p))
    :returns (info smt-fixtype-info-p)
    (b* ((type (smt-type-fix type))
         (acc (smt-fixtype-info-fix acc))
         (kind (smt-type-kind type)))
      (case kind
        (:array (generate-fixtype-info-array name type acc))
        (:sum (generate-fixtype-info-sum name type acc))
        (:abstract acc))))

  (define generate-one-fixtype-info ((type smt-fixtype-p)
                                     (acc smt-fixtype-info-p))
    :returns (info smt-fixtype-info-p)
    (b* ((type (smt-fixtype-fix type))
         (acc (smt-fixtype-info-fix acc))
         ((smt-fixtype f) type)
         (rec-acc (generate-info-pair f.recognizer f.name :recognizer acc))
         (fix-acc (generate-info-pair f.fixer f.name :fixer rec-acc)))
      (generate-fixtype-info-kind f.name f.kind fix-acc)))

  (define generate-fixtype-info ((types smt-fixtype-list-p)
                                 (acc smt-fixtype-info-p))
    :returns (info smt-fixtype-info-p)
    :measure (len types)
    (b* ((types (smt-fixtype-list-fix types))
         (acc (smt-fixtype-info-fix acc))
         ((unless (consp types)) acc)
         ((cons first rest) types)
         (new-acc (generate-one-fixtype-info first acc)))
      (generate-fixtype-info rest new-acc)))

  (define add-fixtype-info ((hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    (b* ((hint (smtlink-hint-fix hint))
         ((smtlink-hint h) hint)
         (info (generate-fixtype-info h.types nil)))
      (change-smtlink-hint hint :types-info info)))

  (define is-type ((x symbolp) (fixtypes smt-fixtype-list-p))
    :returns (type maybe-smt-fixtype-p)
    :measure (len fixtypes)
    (b* ((fixtypes (smt-fixtype-list-fix fixtypes))
         ((unless (consp fixtypes)) nil)
         ((cons first rest) fixtypes)
         ((if (equal x (smt-fixtype->recognizer first))) first))
      (is-type x rest)))

  (define is-recognizer ((x symbolp) (fixinfo smt-fixtype-info-p))
    :returns (okp booleanp)
    (b* ((fixinfo (smt-fixtype-info-fix fixinfo))
         (item (assoc-equal x fixinfo))
         ((unless item) nil)
         ((info-pair p) (cdr item)))
      (equal p.fn-type :recognizer)))

  (define is-fixer ((x symbolp) (fixinfo smt-fixtype-info-p))
    :returns (okp booleanp)
    (b* ((fixinfo (smt-fixtype-info-fix fixinfo))
         (item (assoc-equal x fixinfo))
         ((unless item) nil)
         ((info-pair p) (cdr item)))
      (equal p.fn-type :fixer)))

  (define name-of-recognizer ((x symbolp) (fixinfo smt-fixtype-info-p))
    :returns (name symbolp)
    (b* ((fixinfo (smt-fixtype-info-fix fixinfo))
         (item (assoc-equal x fixinfo))
         ((unless item) nil)
         ((info-pair p) (cdr item)))
      p.name))

  (define fncall-of-fixtypes ((x symbolp) (fixinfo smt-fixtype-info-p))
    :returns (ok booleanp)
    (b* ((fixinfo (smt-fixtype-info-fix fixinfo)))
      (not (null (assoc-equal x fixinfo)))))

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
                       (fixinfo smt-fixtype-info-p))
    :returns (is-decl? booleanp)
    (b* (;; ((if (is-type-hyp-decl expr)) t)
         ((unless (equal (len expr) 2))
          nil)
         (fn-name (car expr))
         ((unless (symbolp fn-name)) nil)
         ((unless (is-recognizer fn-name fixinfo))
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
                    (is-recognizer (car expr) fixinfo)
                    (symbolp (cadr expr)) (cadr expr)))
      :name type-decl-p-definition)))

  (define return-type-of-function ((f smt-function-p)
                                   (fixinfo smt-fixtype-info-p))
    :returns (type symbolp)
    (b* ((f (smt-function-fix f))
         ((smt-function f) f)
         ((unless (and (consp f.returns)
                       (null (cdr f.returns))))
          (er hard? 'hint-interface=>return-type-of-function
              "Smtlink only supports functions that return one value, but ~p0
    returns two: ~p1~%" f.name f.returns))
         (type-thm (hint-pair->thm (decl->type (car f.returns))))
         ((unless (type-decl-p type-thm fixinfo))
          (er hard? 'hint-interface=>return-type-of-function
              "Not a type declaration: ~p0~%" type-thm)))
      (car type-thm)))
  )
