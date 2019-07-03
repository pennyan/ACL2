;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (Canada Day, 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "translate-constant")

(local (in-theory (enable int-to-rat-p
                          string-or-symbol-p
                          word-p)))

;; translate a type name
(define translate-type ((type symbolp)
                        (sym symbolp)
                        (int-to-rat int-to-rat-p))
  :returns (translated word-p)
  (b* ((type (symbol-fix type))
       (item (if (and (equal type 'integerp)
                      (or (equal int-to-rat 't)
                          (and (consp int-to-rat)
                               (member-equal sym int-to-rat))))
                 (assoc-equal 'rationalp *SMT-types*)
               (assoc-equal type *SMT-types*)))
       ((unless (endp item)) (cdr item)))
    (str::downcase-string (lisp-to-python-names type))))

;; translate a type declaration
(define translate-declaration ((name symbolp) (type symbolp)
                               (fixtypes smt-fixtype-list-p)
                               (int-to-rat int-to-rat-p))
  :returns (translated paragraph-p)
  (b* ((name (symbol-fix name))
       (type (symbol-fix type))
       (translated-name (translate-symbol name))
       (translated-type
        (translate-type (name-of-recognizer type fixtypes) name int-to-rat)))
    `(,translated-name = "z3.Const" #\( #\' ,translated-name #\' #\, #\Space
                       ,translated-type #\) #\Newline)))

(define translate-type-decl-list ((type-decl-lst decl-list-p)
                                  (fixtypes smt-fixtype-list-p)
                                  (int-to-rat int-to-rat-p))
  :returns (translated paragraph-p)
  :measure (len type-decl-lst)
  (b* ((type-decl-lst (decl-list-fix type-decl-lst))
       ((unless (consp type-decl-lst)) nil)
       ((cons first rest) type-decl-lst)
       ((decl d) first)
       ((hint-pair h) d.type)
       ((unless (type-decl-p h.thm fixtypes))
        (er hard? 'translate-type=>translate-type-decl-list
            "Type theorem is not a type-decl-p: ~q0"
            h.thm))
       (translated-type-decl
        (translate-declaration d.name (cadr h.thm) fixtypes int-to-rat)))
    (cons translated-type-decl
          (translate-type-decl-list rest fixtypes int-to-rat))))

;; translate symbol type
(local
 (defthm paragraph-p-of-car-of-string-list-fix
   (paragraph-p (car (str::string-list-fix symbols)))
   :hints (("Goal" :in-theory (e/d (paragraph-p word-p str::string-list-fix)
                                   ()))))
 )

(define translate-symbol-declare ((symbols string-listp))
  :returns (translated paragraph-p)
  :measure (len symbols)
  (b* ((symbols (str::string-list-fix symbols))
       ((unless (consp symbols)) nil)
       ((cons first rest) symbols))
    (cons `(,first " = Symbol_z3.intern('" ,first "')" #\Newline)
          (translate-symbol-declare rest))))

(define translate-symbol-enumeration ((symbols string-listp))
  :returns (translated paragraph-p)
  (b* ((datatype-line '("Symbol_z3 = _SMT_.Symbol()" #\Newline))
       (declarations (translate-symbol-declare symbols)))
    `(,datatype-line
      ,@declarations)))


;; translate fixtype definition
(define translate-fixtypes ((fixtypes smt-fixtype-list-p)
                            (int-to-rat int-to-rat-p))
  :returns (mv (translated-fixtypes paragraph-p)
               (fixtype-precond pseudo-term-listp))
  :irrelevant-formals-ok t
  :ignore-ok t
  (mv nil nil))
