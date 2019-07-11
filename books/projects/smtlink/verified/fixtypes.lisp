;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (July 3rd 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "misc/eval" :dir :system)
(include-book "smt-hint-table")

(defalist symbol-symbol-alist
  :key-type symbolp
  :val-type symbolp
  :pred symbol-symbol-alistp
  :true-listp t)

(defthm cdr-of-symbol-symbol-alistp
  (implies (symbol-symbol-alistp x)
           (symbol-symbol-alistp (cdr x))))

(defprod prodkeywords
  ((name symbolp)
   (constructor symbolp)
   (destructors symbol-symbol-alistp)))

(deflist prodkeywords-list
  :elt-type prodkeywords-p
  :true-listp t)

(defprod sumkeywords
  ((name symbolp)
   (rec symbolp)
   (fix symbolp)
   (fix-thm symbolp)
   (basicp symbolp)
   (prods prodkeywords-list-p)))

(defprod arraykeywords
  ((name symbolp)
   (rec symbolp)
   (fix symbolp)
   (fix-thm symbolp)
   (basicp symbolp)
   (store symbolp)
   (select symbolp)
   (key-type symbolp)
   (val-type symbolp)))

(defprod abstractkeywords
  ((name symbolp)
   (rec symbolp)
   (fix symbolp)
   (fix-thm symbolp)
   (basicp symbolp)))

(define def-destructors ((destructors symbol-symbol-alistp))
  :returns (fn-lst smt-function-list-p)
  :measure (len destructors)
  :hints (("Goal"
           :in-theory (enable symbol-symbol-alist-fix)))
  (b* ((destructors (symbol-symbol-alist-fix destructors))
       ((unless (consp destructors)) nil)
       ((cons (cons name type) rest) destructors))
    (cons (make-smt-function :name name
                             :returns
                             `(,(make-decl
                                 :name 'x
                                 :type (make-hint-pair :thm `(,type x)))))
          (def-destructors rest))))

(define def-prod ((prod prodkeywords-p))
  :returns (p prod-p)
  (b* ((prod (prodkeywords-fix prod))
       ((prodkeywords p) prod)
       (constructor (make-smt-function :name p.constructor))
       (destructors (def-destructors p.destructors)))
    (make-prod :kind p.name
               :constructor constructor
               :destructors destructors
               :theorems nil)))

(define def-prod-list ((prod-lst prodkeywords-list-p))
  :returns (pd-lst prod-list-p)
  :measure (len prod-lst)
  :hints (("Goal"
           :in-theory (enable prodkeywords-list-fix)))
  (b* ((prod-lst (prodkeywords-list-fix prod-lst))
       ((unless (consp prod-lst)) nil)
       ((cons first rest) prod-lst))
    (cons (def-prod first)
          (def-prod-list rest))))

(define def-sum-kind ((prod-lst prodkeywords-list-p))
  :returns (sum smt-type-p)
  (make-smt-type-sum :prods (def-prod-list prod-lst)))

(define def-sum-fixtype ((keywords sumkeywords-p))
  (b* ((keywords (sumkeywords-fix keywords))
       ((sumkeywords s) keywords)
       (fix-thm-hint-pair
        `(hint-pair 'nil
                    '(:expand ((,s.rec x) (,s.fix x))
                              :in-theory (disable ,s.rec ,s.fix))
                    ',s.fix-thm))
       (type-event
        `(smt-fixtype ',s.name ',s.rec ',s.fix ,fix-thm-hint-pair ',s.basicp
                      (def-sum-kind ',s.prods)))
       (update-table
        `((add-type :default ,type-event (w state)))))
    `(with-output
       (progn ,@update-table))))

(defmacro defsmtlist (name &key (rec 'nil) (fix 'nil) (fix-thm 'nil)
                           (basicp 'nil)
                           (cons 'nil) (car 'nil)
                           (cdr 'nil) (nil-fn 'nil)
                           (elt-type 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp rec)
                              (symbolp fix)
                              (symbolp fix-thm)
                              (symbolp basicp)
                              (symbolp cons)
                              (symbolp car)
                              (symbolp cdr)
                              (symbolp nil-fn)
                              (symbolp elt-type))))
  `(make-event
    (b* (((if (or (null ',rec) (null ',fix) (null ',fix-thm)
                  (null ',cons) (null ',car) (null ',cdr) (null ',nil-fn)
                  (null ',elt-type)))
          (er hard? 'fixtypes=>defsmtlist "Keywords for defsmtlist are :rec,
  :fix, :fix-thm, :basicp, :cons, :car, :cdr, :nil-fn and :elt-type.~%"))
         (cons-prod-fns '((,car . ,elt-type)
                          (,cdr . ,rec)))
         (cons-prod (prodkeywords 'cons ',cons cons-prod-fns))
         (nil-prod (prodkeywords 'nil ',nil-fn nil)))
    (def-sum-fixtype (sumkeywords ',name ',rec ',fix ',fix-thm ',basicp
                                  (list cons-prod nil-prod))))))

;; this is a test
(must-succeed
(defsmtlist int-list
  :rec int-list-p
  :fix int-list-fix
  :fix-thm int-list-fix-when-int-list-p
  :cons int-list-cons
  :car int-list-car
  :cdr int-list-cdr
  :nil-fn int-list-nil
  :elt-type integerp
  )
)

(defmacro defsmtprod (name &key (rec 'nil) (fix 'nil) (fix-thm 'nil) (basicp 'nil)
                           (constructor 'nil) (destructors 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp rec)
                              (symbolp fix)
                              (symbolp fix-thm)
                              (symbolp basicp)
                              (symbolp constructor)
                              (symbol-symbol-alistp destructors))))
  `(make-event
    (b* (((if (or (null ',rec) (null ',fix) (null ',fix-thm)
                  (null ',constructor) (null ',destructors)))
          (er hard? 'fixtypes=>defsmtprod "Keywords for defsmtprod are :rec,
  :fix, :fix-thm, :basicp, :constructor and :destructors. ~%"))
         (prod-list `(,(make-prodkeywords :name ',name
                                          :constructor ',constructor
                                          :destructors ',destructors))))
      (def-sum-fixtype (sumkeywords ',name ',rec ',fix ',fix-thm ',basicp prod-list)))))

;; this is a test
(must-succeed
 (defsmtprod animal
   :rec animal-p
   :fix animal-fix
   :fix-thm animal-fix-when-animal-p
   :constructor animal
   :destructors ((body . body-p) (legs . leg-list-p))
   )
 )

(defmacro defsmtoption (name &key (rec 'nil) (fix 'nil) (fix-thm 'nil) (basicp 'nil)
                             (some-constructor 'nil) (some-destructor 'nil)
                             (nil-constructor 'nil) (some-type 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp rec)
                              (symbolp fix)
                              (symbolp fix-thm)
                              (symbolp basicp)
                              (symbolp some-constructor)
                              (symbolp some-destructor)
                              (symbolp nil-constructor)
                              (symbolp some-type))))
  `(make-event
    (b* (((if (or (null ',rec) (null ',fix) (null ',fix-thm)
                  (null ',some-constructor) (null ',some-destructor)
                  (null ',nil-constructor) (null ',some-type)))
          (er hard? 'fixtypes=>defsmtoption "Keywords for defsmtprod are :rec,
  :fix, :fix-thm, :basicp, :some-constructor, :some-destructor,
                             :nil-constructor and :some-type.~%"))
         (some-prod-destructors '((,some-destructor . ,some-type)))
         (some-prod (make-prodkeywords
                     :name 'some
                     :constructor ',some-constructor
                     :destructors some-prod-destructors))
         (none-prod (make-prodkeywords
                     :name 'none
                     :constructor ',nil-constructor
                     :destructors nil)))
      (def-sum-fixtype (sumkeywords ',name ',rec ',fix ',fix-thm ',basicp
                                    (list some-prod none-prod))))))

;; this is a test
(must-succeed
 (defsmtoption maybe-int
   :rec maybe-int-p
   :fix maybe-int-fix
   :fix-thm maybe-int-fix-when-maybe-int-p
   :some-constructor maybe-int-some
   :some-destructor maybe-int-some->val
   :nil-constructor maybe-int-none
   :some-type integerp
   )
 )

(define input-prods-to-keywords ((prods))
  :returns (pl prodkeywords-list-p)
  (b* (((unless (consp prods)) nil)
       ((cons first rest) prods)
       ((unless (equal (len first) 5))
        (input-prods-to-keywords rest))
       ((list name & constructor & destructors) first)
       ((unless (and (symbolp name)
                     (symbolp constructor)
                     (symbol-symbol-alistp destructors)))
        (input-prods-to-keywords rest)))
    (cons (prodkeywords name constructor destructors)
          (input-prods-to-keywords rest))))

(defmacro defsmtsum (name &key (rec 'nil) (fix 'nil) (fix-thm 'nil) (basicp 'nil)
                          (prods 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp rec)
                              (symbolp fix)
                              (symbolp fix-thm)
                              (symbolp basicp))))
  `(make-event
    (b* (((if (or (null ',rec) (null ',fix) (null ',fix-thm)))
          (er hard? 'fixtypes=>defsmtsum "Keywords for defsmtsum are :rec,
  :fix, :fix-thm, :basicp and :prods.~%"))
         (prodkeyword-lst (input-prods-to-keywords ',prods)))
      (def-sum-fixtype (sumkeywords ',name ',rec ',fix ',fix-thm ',basicp
                                    prodkeyword-lst)))))

(must-succeed
 (defsmtsum arithtm
   :rec arithtm-p
   :fix arithtm-fix
   :fix-thm arithtm-fix-when-arithtm-p
   :prods ((:num :constructor arithtm-num
                 :destructors ((val . integerp)))
           (:plus :constructor arithtm-plus
                  :destructors ((left . arithtm-p)
                                (right . arithtm-p)))
           (:minus :constructor arithtm-minus
                   :destructors ((arg . arithtm-p))))
   )
 )

(define def-array-fixtype ((keywords arraykeywords-p))
  (b* ((keywords (arraykeywords-fix keywords))
       ((arraykeywords a) keywords)
       (fix-thm-hint-pair
        `(hint-pair 'nil
                    '(:expand ((,a.rec x) (,a.fix x))
                              :in-theory (disable ,a.rec ,a.fix))
                    ',a.fix-thm))
       (store-fn (make-smt-function :name a.store))
       (select-fn (make-smt-function :name a.select))
       (array-kind (make-smt-type-array :store store-fn
                                        :select select-fn
                                        :key-type a.key-type
                                        :val-type a.val-type
                                        :theorems nil))
       (type-event
        `(smt-fixtype ',a.name ',a.rec ',a.fix ,fix-thm-hint-pair ',a.basicp
                      ',array-kind))
       (update-table
        `((add-type :default ,type-event (w state)))))
    `(with-output
       (progn ,@update-table))))

(defmacro defsmtarray (name &key (rec 'nil) (fix 'nil) (fix-thm 'nil) (basicp 'nil)
                            (store 'nil) (select 'nil) (key-type 'nil)
                            (val-type 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp rec)
                              (symbolp fix)
                              (symbolp fix-thm)
                              (symbolp basicp)
                              (symbolp store)
                              (symbolp select)
                              (symbolp key-type)
                              (symbolp val-type))))
  `(make-event
    (b* (((if (or (null ',rec) (null ',fix) (null ',fix-thm)
                  (null ',store) (null ',select) (null ',key-type) (null ',val-type)))
          (er hard? 'fixtypes=>defsmtarray "Keywords for defsmtsum are :rec,
  :fix, :fix-thm, :basicp, :store, :select, :key-type and :val-type.~%")))
      (def-array-fixtype (arraykeywords ',name ',rec ',fix ',fix-thm ',basicp
                                        ',store ',select ',key-type ',val-type)))))

(must-succeed
 (defsmtarray int-int-array
   :rec int-int-array-p
   :fix int-int-array-fix
   :fix-thm int-int-array-fix-when-int-int-array-p
   :store int-int-array-store
   :select int-int-array-select
   :key-type integerp
   :val-type integerp
   )
 )

(define def-abstract-fixtype ((keywords abstractkeywords-p))
  (b* ((keywords (abstractkeywords-fix keywords))
       ((abstractkeywords a) keywords)
       (fix-thm-hint-pair
        `(hint-pair 'nil
                    '(:expand ((,a.rec x) (,a.fix x))
                              :in-theory (disable ,a.rec ,a.fix))
                    ',a.fix-thm))
       (type-event
        `(smt-fixtype ',a.name ',a.rec ',a.fix ,fix-thm-hint-pair ',a.basicp
                      (make-smt-type-abstract)))
       (update-table
        `((add-type :default ,type-event (w state)))))
    `(with-output
       (progn ,@update-table))))

(defmacro defsmtabstract (name &key (rec 'nil) (fix 'nil) (fix-thm 'nil)
                               (basicp 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp rec)
                              (symbolp fix)
                              (symbolp fix-thm)
                              (symbolp basicp))))
  `(make-event
    (b* (((if (or (null ',rec) (null ',fix) (null ',fix-thm)))
          (er hard? 'fixtypes=>defsmtabstract "Keywords for defsmtabstract are :rec,
  :fix, :fix-thm and :basicp.~%")))
      (def-abstract-fixtype (abstractkeywords ',name ',rec ',fix ',fix-thm ',basicp)))))

(must-succeed
 (defsmtabstract abstract
   :rec abstract-p
   :fix abstract-fix
   :fix-thm abstract-fix-when-abstract-p
   )
 )

;; ------------------------------------------------------
;; When certifying this book, several basic types are put into the
;; smt-hint-table :default smtlink-hint

(defthm ifix-when-integerp
  (implies (integerp x)
           (equal (ifix x) x)))
(defsmtabstract integer
  :rec integerp
  :fix integer-fix
  :fix-thm ifix-when-integerp
  :basicp t)

(defthm bool-fix$inline-when-booleanp
  (implies (booleanp x)
           (equal (bool-fix$inline x) x)))
(defsmtabstract boolean
  :rec booleanp
  :fix bool-fix$inline
  :fix-thm bool-fix$inline-when-booleanp
  :basicp t)

(defthm symbol-fix-when-symbolp
  (implies (symbolp x)
           (equal (symbol-fix x) x)))
(defsmtabstract symbol
  :rec symbolp
  :fix symbol-fix
  :fix-thm symbol-fix-when-symbolp
  :basicp t)

(defthm rfix-when-rationalp
  (implies (rationalp x)
           (equal (rfix x) x)))
(defsmtabstract rational
  :rec rationalp
  :fix rfix
  :fix-thm rfix-when-rationalp
  :basicp t)

(defthm realfix-when-real/rationalp
  (implies (real/rationalp x)
           (equal (realfix x) x)))
(defsmtabstract real
  :rec realp
  :fix realfix
  :fix-thm realfix-when-realp
  :basicp t)
(defsmtabstract real/rational
  :rec real/rationalp
  :fix realfix
  :fix-thm realfix-when-real/rationalp
  :basicp t)
