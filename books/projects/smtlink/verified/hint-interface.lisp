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
(include-book "../utils/pseudo-term")
(include-book "fty")

;; (defsection SMT-hint-interface
;;   :parents (verified)
;;   :short "Define default Smtlink hint interface"

  ;; -------------------------------------------------------
  ;;
  ;; Define default Smtlink hint interface
  ;;
  ;;  One needs to attach to SMT-hint their own aggregate
  ;;    to pass in a different hint.
  ;;

  (defprod hint-pair
    :parents (smtlink-hint)
    ((thm pseudo-termp :default nil)       ;; a theorem statement about the variable
     (hints true-listp :default nil)     ;; the hint for proving this theorem
     )
    :verbosep t)

  (deflist hint-pair-list
    :parents (hint-pair)
    :elt-type hint-pair
    :pred hint-pair-listp
    :true-listp t)

  (define decl->type-reqfix ((x hint-pair-p))
    :returns (fixed hint-pair-p)
    (b* ((x (hint-pair-fix x))
         (thm (hint-pair->thm x))
         (hints (hint-pair->hints x)))
      (make-hint-pair :thm (if (symbolp thm) thm nil)
                      :hints (acl2::true-list-fix hints))))

  (local (in-theory (enable decl->type-reqfix)))
  (defprod decl
    :parents (smtlink-hint)
    ((name symbolp :default nil)
     (type hint-pair-p :default (make-hint-pair) :reqfix (decl->type-reqfix type)))
    :require (symbolp (hint-pair->thm type)))

  (deflist decl-list
    :parents (decl)
    :elt-type decl
    :pred decl-listp
    :true-listp t)

  ;; (defalist decl-alist
  ;;   :key-type symbol
  ;;   :val-type decl
  ;;   :pred decl-alistp)

  ;; (define make-alist-decl-list ((decl-lst decl-listp))
  ;;   :returns (decl-alist decl-alistp)
  ;;   :measure (len decl-lst)
  ;;   (b* ((decl-lst (decl-list-fix decl-lst))
  ;;        ((unless (consp decl-lst)) nil)
  ;;        ((cons first rest) decl-lst)
  ;;        ((decl d) first))
  ;;     (cons (cons d.name d) (make-alist-decl-list rest))))

  (defprod func
    :parents (smtlink-hint)
    ((name symbolp :default nil)
     (formals decl-listp :default nil)
     (guard hint-pair-p :default (make-hint-pair))
     (returns decl-listp :default nil)            ;; belong to auxiliary hypotheses
     (more-returns hint-pair-listp :default nil)  ;; belong to auxiliary hypotheses
     (expansion-depth natp :default 1)
     (flattened-formals symbol-listp :default nil)
     (flattened-returns symbol-listp :default nil)))

  (deflist func-list
    :parents (func)
    :elt-type func
    :pred func-listp
    :true-listp t)

  (defalist func-alist
    :key-type symbol
    :val-type func
    :true-listp t
    :pred func-alistp)

  (defprod binding
    :parents (smtlink-hint)
    ((var symbolp :default nil)
     (expr pseudo-termp :default nil)
     (type symbolp :default nil)))

  (deflist binding-list
    :parents (binding)
    :elt-type binding
    :pred binding-listp
    :true-listp t)

  (defprod let-binding
    :parents (smtlink-hint)
    ((bindings binding-listp :default nil)
     (hypotheses hint-pair-listp :default nil)))

  ;; The hint structure that contain all hints for the verified clause
  ;; processor.
  ;;
  ;; Fields:
  ;; User fields:
  ;; 1. functions: function definitions.
  ;; 2. hypotheses: hypotheses to the G theorem.
  ;; 3. main-hint: hints to the G' -> G theorem.
  ;; 4. let-binding: binds expressions to variables, generalization.
  ;; 5. fty: a list of fty types used in the theorem. Will be treated as
  ;; algebraic datatypes in SMT solver.
  ;; 6. int-to-rat: converts all integers to rationals.
  ;; 7. smt-dir: where to put the generated python files. Default /tmp/z3_files
  ;; 8. rm-file: configuration for whether to remove generated files.
  ;; 9. smt-fname: configure the name of generated SMT theorem file.
  ;; 10. smt-params: hints for parameter tuning of the SMT solver.
  ;;
  ;; Internal fields:
  ;; 11. fty-info: an alist from fty functions to fty-info-p
  ;; 12. fty-types: contains all fty type definitions for translation
  ;; 13. fast-functions: internal field for storing a fast version of function
  ;; definitions. Might be able to make the functions field a fast one after
  ;; changing the user interface.
  ;; 14. aux-hint-list: internal field for making a list of auxiliary hints.
  ;; 15. type-decl-list: internal field for making a list of auxiliary type
  ;; hints.
  ;; 16. expanded-clause-w/-hint: internal field for storing the SMT theorem.
  ;; 17. expanded-G/type: clause without type
  ;; 18. smt-cnf: configuration for connection to the SMT solver.
  ;; 19. wrld-fn-len: a number specifying the upper bound of the length of the
  ;; current world. It sets a limit to the expansion depth to take care of
  ;; recursive function expansion. This will only ensure termination proof of
  ;; the expand function, but it doesn't guarantee performance since the world
  ;; length can be extremely large, and expansion is exponential. Performance
  ;; is replied upon user who will specify which functions are recursive and
  ;; therefore will be expanded only by a given number of levels.
  ;; 20. custom-p: Used custom version of Smtlink or not. Default nil.
  ;;
  (defprod smtlink-hint
    :parents (SMT-hint-interface)
    ((functions func-listp :default nil)
     (hypotheses hint-pair-listp :default nil)
     (main-hint true-listp :default nil)
     (let-binding let-binding-p :default (make-let-binding))
     (symbols symbol-listp :default nil)
     (abs symbol-listp :default nil)
     (fty symbol-listp :default nil)
     (fty-info fty-info-alist-p :default nil)
     (fty-types fty-types-p :default nil)
     (int-to-rat booleanp :default nil)
     (smt-dir stringp :default "")
     (rm-file booleanp :default t)
     (smt-fname stringp :default "")
     (smt-params true-listp :default nil)
     (fast-functions func-alistp :default nil)
     (type-decl-list pseudo-termp :default nil)
     (expanded-clause-w/-hint hint-pair-p :default (make-hint-pair))
     (expanded-G/type pseudo-termp :default nil)
     (smt-cnf smtlink-config-p :default (make-smtlink-config))
     (wrld-fn-len natp :default 0)
     (custom-p booleanp :default nil)))

  (defoption maybe-smtlink-hint smtlink-hint-p
    :parents (smtlink-hint))

  (define flatten-formals/returns ((formal/return-lst decl-listp))
    :returns (flattened-lst symbol-listp)
    :measure (len formal/return-lst)
    :hints (("Goal" :in-theory (enable decl-list-fix)))
    (b* ((formal/return-lst (decl-list-fix formal/return-lst))
         ((if (endp formal/return-lst)) nil)
         ((cons first rest) formal/return-lst)
         ((decl d) first))
      (cons d.name (flatten-formals/returns rest))))

  (define make-alist-fn-lst ((fn-lst func-listp))
    :parents (SMT-hint-interface)
    :short "@(call make-alist-fn-lst) makes fn-lst a fast alist"
    :returns (fast-fn-lst func-alistp)
    :measure (len fn-lst)
    (b* ((fn-lst (func-list-fix fn-lst))
         ((unless (consp fn-lst)) nil)
         ((cons first rest) fn-lst)
         ((func f) first)
         (new-f (change-func f
                             :flattened-formals (flatten-formals/returns f.formals)
                             :flattened-returns (flatten-formals/returns f.returns))))
      (cons (cons f.name new-f) (make-alist-fn-lst rest))))

  (defconst *default-smtlink-hint*
    (make-smtlink-hint))


  ;; (defstub smt-hint () => *)
  (encapsulate
    (((smt-hint) => *))
    (local (define smt-hint () (make-smtlink-hint)))
    (defthm smtlink-p-of-smt-hint
      (smtlink-hint-p (smt-hint)))
    )

  (define default-smtlink-hint ()
    (change-smtlink-hint *default-smtlink-hint*))

  (defattach smt-hint default-smtlink-hint)

;;  )
