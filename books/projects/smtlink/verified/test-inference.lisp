(in-package "SMT")
(include-book "type-inference-bottomup")
(include-book "type-inference-topdown")
(set-state-ok t)

(defalist rational-integer-alist
  :key-type rationalp
  :val-type integerp
  :pred rational-integer-alistp
  :true-listp t)

(define rational-integer-cons-p ((x t))
  (and (consp x)
       (rationalp (car x))
       (integerp (cdr x))))

(easy-fix rational-integer-cons (cons 0 0))

(defoption maybe-integerp integerp :pred maybe-integerp)

(defoption maybe-rational-integer-consp rational-integer-cons-p
  :pred maybe-rational-integer-consp)

(defun supertype ()
  `((integerp . (rationalp maybe-integerp))
    (rationalp . nil)
    (symbolp . nil)
    (booleanp . nil)
    (rational-integer-cons-p . (maybe-rational-integer-consp))
    (rational-integer-alistp . nil)
    (maybe-integerp . nil)
    (maybe-rational-integer-consp . nil)
    ))

(defun subtype ()
  `((rationalp . (integerp))
    (maybe-integerp . (integerp))
    (integerp . nil)
    (symbolp . nil)
    (booleanp . nil)
    (maybe-rational-integer-consp . (rational-integer-cons-p))
    (rational-integer-alistp . nil)
    (rational-integer-cons-p . nil)
    ))

(defthm integerp-implies-maybe-integerp
  (implies (integerp x) (maybe-integerp x)))

(defthm integerp-implies-rationalp
  (implies (integerp x) (rationalp x)))

(defthm rational-integer-cons-p-implies-maybe-rational-integer-consp
  (implies (rational-integer-cons-p x) (maybe-rational-integer-consp x)))

(defun supertype-thm ()
  `((,(make-type-tuple :type 'integerp :neighbour-type 'maybe-integerp) .
     integerp-implies-maybe-integerp)
    (,(make-type-tuple :type 'integerp :neighbour-type 'rationalp) .
     integerp-implies-rationalp)
    (,(make-type-tuple :type 'rational-integer-cons-p
                       :neighbour-type 'maybe-rational-integer-consp) .
                       rational-integer-cons-p-implies-maybe-rational-integer-consp)))

(defthm maybe-integerp-can-be-integerp
  (implies (and (maybe-integerp x) x)
           (integerp x)))

(defthm maybe-rational-integer-consp-can-be-rational-integer-cons-p
  (implies (and (maybe-rational-integer-consp x) x)
           (rational-integer-cons-p x)))

(defun subtype-thm ()
  `((,(make-type-tuple :type 'maybe-integerp :neighbour-type 'integerp) .
     maybe-integerp-can-be-integerp)
    (,(make-type-tuple :type 'maybe-rational-integer-consp
                       :neighbour-type 'rational-integer-cons-p) .
                       maybe-rational-integer-consp-can-be-rational-integer-cons-p)))

(defthm return-of-assoc-equal
  (implies (and (rationalp y)
                (rational-integer-alistp x))
           (maybe-rational-integer-consp (assoc-equal y x)))
  :hints (("Goal" :in-theory (enable maybe-rational-integer-consp
                                     rational-integer-cons-p))))

(defthm return-of-cdr-maybe
  (implies (maybe-rational-integer-consp x)
           (maybe-integerp (cdr x)))
  :hints (("Goal" :in-theory (enable maybe-rational-integer-consp
                                     rational-integer-cons-p))))

(defthm return-of-cdr
  (implies (rational-integer-cons-p x)
           (integerp (cdr x)))
  :hints (("Goal" :in-theory (enable rational-integer-cons-p))))

(defthm return-of-<
  (implies (and (rationalp x)
                (rationalp y))
           (booleanp (< x y))))

(defthm return-of-binary-+
  (implies (and (integerp x)
                (integerp y))
           (integerp (binary-+ x y))))

(defthm return-of-binary-+-rationalp
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (binary-+ x y))))

(defthm return-of-unary--
  (implies (integerp x)
           (integerp (unary-- x))))

(defthm return-of-unary---rationalp
  (implies (rationalp x)
           (rationalp (unary-- x))))

(defthm return-of-rational-integer-alistp
  (booleanp (rational-integer-alistp x)))

(defthm return-of-rationalp
  (booleanp (rationalp x)))

(defthm return-of-integerp
  (booleanp (integerp x)))

(defthm return-of-acons
  (implies (and (rationalp x)
                (integerp y)
                (rational-integer-alistp z))
           (rational-integer-alistp (acons x y z))))

;; assoc-equal: rational-integer-alistp -> maybe-rational-integer-consp
;; cdr: maybe-rational-integer-consp -> maybe-integerp &
;;      rational-integer-consp -> integerp
;; <: integerp integerp -> booleanp
;; binary-+: integerp integerp -> integerp
;; unary--: integerp -> integerp
(defun functions ()
  `((acons
     . ,(make-arg-decl-next
         :next `((rationalp
                  . ,(make-arg-decl-next
                      :next `((integerp
                               . ,(make-arg-decl-next
                                   :next `((rational-integer-alistp
                                            . ,(make-arg-decl-done
                                                :r
                                                (make-return-spec
                                                 :formals '(x y z)
                                                 :return-type 'rational-integer-alistp
                                                 :returns-thm 'return-of-acons))))))))))))
    (assoc-equal
     . ,(make-arg-decl-next
         :next `((rationalp
                  . ,(make-arg-decl-next
                      :next `((rational-integer-alistp
                               . ,(make-arg-decl-done
                                   :r (make-return-spec
                                       :formals '(y x)
                                       :return-type 'maybe-rational-integer-consp
                                       :returns-thm 'return-of-assoc-equal)))))))))
    (cdr
     . ,(make-arg-decl-next
         :next `((maybe-rational-integer-consp
                  . ,(make-arg-decl-done
                      :r (make-return-spec
                          :formals '(x)
                          :return-type 'maybe-integerp
                          :returns-thm 'return-of-cdr-maybe)))
                 (rational-integer-cons-p
                  . ,(make-arg-decl-done
                      :r (make-return-spec
                          :formals '(x)
                          :return-type 'integerp
                          :returns-thm 'return-of-cdr))))))
    (<
     . ,(make-arg-decl-next
         :next `((rationalp
                  . ,(make-arg-decl-next
                      :next `((rationalp
                               . ,(make-arg-decl-done
                                   :r (make-return-spec
                                       :formals '(x y)
                                       :return-type 'booleanp
                                       :returns-thm 'return-of-<)))))))))
    (binary-+
     . ,(make-arg-decl-next
         :next `((integerp
                  . ,(make-arg-decl-next
                      :next `((integerp
                               . ,(make-arg-decl-done
                                   :r (make-return-spec
                                       :formals '(x y)
                                       :return-type 'integerp
                                       :returns-thm
                                       'return-of-binary-+))))))
                 (rationalp
                  . ,(make-arg-decl-next
                      :next `((rationalp
                               . ,(make-arg-decl-done
                                   :r (make-return-spec
                                       :formals '(x y)
                                       :return-type 'rationalp
                                       :returns-thm 'return-of-binary-+-rationalp)))))))))
    (unary-- . ,(make-arg-decl-next
                 :next `((integerp . ,(make-arg-decl-done
                                       :r (make-return-spec
                                           :formals '(x)
                                           :return-type 'integerp
                                           :returns-thm
                                           'return-of-unary--)))
                         (rationalp . ,(make-arg-decl-done
                                        :r (make-return-spec
                                            :formals '(x)
                                            :return-type 'rationalp
                                            :returns-thm
                                            'return-of-unary---rationalp))))))
    (rational-integer-alistp . ,(make-arg-decl-next
                                 :next `((t . ,(make-arg-decl-done
                                                :r (make-return-spec
                                                    :formals '(x)
                                                    :return-type 'booleanp
                                                    :returns-thm
                                                    'return-of-rational-integer-alistp))))))
    (rationalp . ,(make-arg-decl-next
                   :next `((t . ,(make-arg-decl-done
                                  :r (make-return-spec
                                      :formals '(x)
                                      :return-type 'booleanp
                                      :returns-thm
                                      'return-of-rationalp))))))
    (integerp . ,(make-arg-decl-next
                  :next `((t . ,(make-arg-decl-done
                                 :r (make-return-spec
                                     :formals '(x)
                                     :return-type 'booleanp
                                     :returns-thm
                                     'return-of-integerp))))))
    ))

(defun basic ()
  `((integerp . ,(make-basic-type-description :recognizer 'integerp
                                              :fixer 'ifix))
    (rationalp . ,(make-basic-type-description :recognizer 'rationalp
                                               :fixer 'rfix))
    (symbolp . ,(make-basic-type-description :recognizer 'symbolp
                                             :fixer 'symbol-fix))
    (booleanp . ,(make-basic-type-description :recognizer 'booleanp
                                             :fixer 'bool-fix))))

(defun consp-info ()
  `((rational-integer-cons-p . ,(make-cons-type-description :recognizer
                                                            'rational-integer-cons-p
                                                            :fixer
                                                            'rational-integer-cons-fix
                                                            :car-type 'rationalp
                                                            :cdr-type 'integerp
                                                            :cdr-thm nil))))

(defun alist ()
  `((rational-integer-alistp . ,(make-alist-type-description :recognizer 'rational-integer-alistp
                                                             :fixer 'rational-integer-alist-fix
                                                             :key-type 'rationalp
                                                             :val-type 'integerp
                                                             :acons-thm nil
                                                             :assoc-equal-thm nil
                                                             ))))

(defun option ()
  `((maybe-integerp . ,(make-option-type-description :recognizer
                                                     'maybe-integerp
                                                     :fixer 'maybe-integer-fix
                                                     :some-type 'integerp
                                                     :some-constructor-thm nil
                                                     :none-constructor-thm nil
                                                     :some-destructor-thm nil
                                                     ))
    (maybe-rational-integer-consp . ,(make-option-type-description :recognizer 'maybe-rational-integer-consp
                                                                   :fixer 'maybe-rational-integer-cons-fix
                                                                   :some-type
                                                                   'rational-integer-cons-p
                                                                   :some-constructor-thm nil
                                                                   :none-constructor-thm nil
                                                                   :some-destructor-thm
                                                                   nil))))

(defun options ()
  (b* ((supertype (supertype))
       (supertype-thm (supertype-thm))
       (subtype (subtype))
       (subtype-thm (subtype-thm))
       (functions (functions))
       (basic (basic))
       (consp (consp-info))
       (list nil)
       (alist (alist))
       (prod nil)
       (option (option))
       (sum nil)
       (abstract nil))
    (make-type-options
     :supertype supertype
     :supertype-thm supertype-thm
     :subtype subtype
     :subtype-thm subtype-thm
     :functions functions
     :basic basic
     :consp consp
     :list list
     :alist alist
     :prod prod
     :option option
     :sum sum
     :abstract abstract)))

(defun term ()
  '(if (if (rational-integer-alistp al)
           (if (rationalp r1)
               (assoc-equal r1 al)
             'nil)
         'nil)
       (< (binary-+ (cdr (assoc-equal r1 al))
                    (unary-- (cdr (assoc-equal r1 al))))
          '2)
     't))

(defun term2 ()
  '(if (if (rational-integer-alistp al)
           (if (rationalp r1)
               (assoc-equal r1 al)
               'nil)
           'nil)
       (< (binary-+ (cdr (assoc-equal r1 al))
                    (unary-- (cdr (assoc-equal r1 al))))
          '2)
     't))

(defun term3 ()
  '(if (if (integerp x)
           (if (rationalp y)
               (if (< '0 y) (< x '0) 'nil)
             'nil)
         'nil)
       (< '0 (binary-+ y (unary-- x)))
     't))

(defun term4 ()
  '(if (if (rational-integer-alistp x)
           (if (integerp y)
               (assoc-equal y (acons '1 '2 x))
             'nil)
         'nil)
       (< '0 (cdr (assoc-equal y (acons '1 '2 x))))
     't))

(defun term5 ()
  '(if (if (rational-integer-alistp al)
           (rationalp r1)
         'nil)
       ((lambda (x y)
          (if (assoc-equal y x)
              (< (binary-+ (cdr (assoc-equal y x))
                           (unary-- (cdr (assoc-equal y x))))
                 '2)
            'nil))
        al r1)
     't))

(type-judgement (term) ''t (options) state)
(type-judgement (term2) ''t (options) state)
(type-judgement (term3) ''t (options) state)
(type-judgement (term4) ''t (options) state)
(type-judgement (term5) ''t (options) state)

;; -----------------------------------------
;; ;; testing guard utilities

;; (defun term5-unquoted (r1 al)
;;   (if (if (rational-integer-alistp al)
;;           (if (rationalp r1)
;;               (assoc-equal r1 al)
;;             'nil)
;;         'nil)
;;       ((lambda (x y)
;;          (< (binary-+ (cdr (assoc-equal y x))
;;                       (unary-- (cdr (assoc-equal y x))))
;;             '2))
;;        al r1)
;;     't))

;; (defun term5 ()
;;   '(if (if (rational-integer-alistp al)
;;            (if (rationalp r1)
;;                (assoc-equal r1 al)
;;              'nil)
;;          'nil)
;;        ((lambda (x y)
;;           (< (binary-+ (cdr (assoc-equal y x))
;;                        (unary-- (cdr (assoc-equal y x))))
;;              '2))
;;         al r1)
;;      't))

;; (verify-guards-formula term5-unquoted)
;; (verify-guards-formula term5-unquoted :guard-simplify nil)
;; (verify-guards-formula (if (if (rational-integer-alistp al)
;;                                (if (rationalp r1)
;;                                    (assoc-equal r1 al)
;;                                  'nil)
;;                              'nil)
;;                            ((lambda (x y)
;;                               (< (binary-+ (cdr (assoc-equal y x))
;;                                            (unary-- (cdr (assoc-equal y x))))
;;                                  '2))
;;                             al r1)
;;                          't)
;;                        :guard-simplify nil)

;; (guard-obligation 'term5-unquoted nil nil nil 'top-level state)
;; (guard-obligation '(if (if (rational-integer-alistp al)
;;                            (if (rationalp r1)
;;                                (assoc-equal r1 al)
;;                              'nil)
;;                          'nil)
;;                        ((lambda (x y)
;;                           (< (binary-+ (cdr (assoc-equal y x))
;;                                        (unary-- (cdr (assoc-equal y x))))
;;                              '2))
;;                         al r1)
;;                      't)
;;                   nil nil nil 'top-level state)

;; (mv-let
;;   (erp val)
;;   (guard-obligation 'term5-unquoted nil nil nil 'top-level state)
;;   (value
;;    (and
;;     (not erp)
;;     (cw "clauses: ~q0" (conjoin-clauses (cadr val))))))

;; (gthm 'term5-unquoted nil nil)
;; (guard-theorem 'term5-unquoted nil nil (w state) state)

;; ;; I needed a translated term, therefore only guard-obligation and
;; ;; guard-theorem is interesting to me.
;; ;; Guard-obligation takes a term but guard-theorem doesn't. I guess I will go
;; ;; with guard-obligation.
;;------------------------------------------------------

(good-typed-term-p
 (make-typed-term :term (term)
                  :path-cond ''t
                  :judgements (type-judgement (term) ''t (options) state))
 (options))

(good-typed-term-p
 (make-typed-term :term (term2)
                  :path-cond ''t
                  :judgements (type-judgement (term2) ''t (options) state))
 (options))

(good-typed-term-p
 (make-typed-term :term (term3)
                  :path-cond ''t
                  :judgements (type-judgement (term3) ''t (options) state))
 (options))

(good-typed-term-p
 (make-typed-term :term (term4)
                  :path-cond ''t
                  :judgements (type-judgement (term4) ''t (options) state))
 (options))

(good-typed-term-p
 (make-typed-term :term (term5)
                  :path-cond ''t
                  :judgements (type-judgement (term5) ''t (options) state))
 (options))


;; ------------------------------------------------------

(unify-type (make-typed-term :term (term)
                             :path-cond ''t
                             :judgements (type-judgement (term) ''t (options)
                                                         state))
            ''t
            (options)
            state)

(unify-type (make-typed-term :term (term2)
                             :path-cond ''t
                             :judgements (type-judgement (term2) ''t (options)
                                                         state))
            ''t
            (options)
            state)

(unify-type (make-typed-term :term (term3)
                             :path-cond ''t
                             :judgements (type-judgement (term3) ''t (options)
                                                         state))
            ''t
            (options)
            state)

(unify-type (make-typed-term :term (term4)
                             :path-cond ''t
                             :judgements (type-judgement (term4) ''t (options)
                                                         state))
            ''t
            (options)
            state)

(unify-type (make-typed-term :term (term5)
                             :path-cond ''t
                             :judgements (type-judgement (term5) ''t (options)
                                                         state))
            ''t
            (options)
            state)
