;; Copyright (C) 2015, University of British Columbia
;; Written by Mark Greenstreet (Dec 18th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(include-book "std/util/top" :dir :system)

(defsection alists
  (encapsulate ;; generic properties of ACL2 alist's
    (((alist-key-p *) => *)
     ((alist-val-p *) => *)
     ((alist-val-as-bool *) => *)
     ((alist-val-default) => *))

    (local (define alist-key-p (x)
             :guard t
             :returns (ok booleanp)
             (and x (symbolp x))))
    (more-returns alist-key-p
                  (ok (booleanp ok) :name booleanp-of-alist-key-p))

    (local (define alist-val-p (x)
             :guard t
             :returns (ok booleanp)
             :enabled t
             (integerp x)))
    (more-returns alist-val-p
                  (ok (booleanp ok) :name booleanp-of-alist-val-p))

    (local (define alist-val-as-bool ((v alist-val-p))
             (declare (ignorable v))
             :returns (ok booleanp)
             t))
    (more-returns alist-val-as-bool
                  (ok (booleanp ok)
                      :name booleanp-of-alist-val-as-bool))

    (local (define alist-val-default ()
             :returns (default-v any-p)
             :enabled t
             0))
    (more-returns alist-val-default
                  (default-v (alist-val-p default-v)
                    :name alist-val-p-of-alist-val-default)))

  (define alist-consp (x)
    :guard t
    :returns (ok booleanp)
    (implies x (and (consp x) (alist-key-p (car x)) (alist-val-p (cdr x)))))

  (define maybe-alist-consp (x)
    :guard t
    :returns (ok booleanp)
    (implies x (alist-consp x)))

  (define maybe-alist-val-p (x)
    :guard t
    :returns (ok booleanp)
    (implies x (alist-val-p x)))

  (define alist-p (al)
    :guard t
    :returns (ok booleanp)
    (if (null al) t
      (and (consp al)
           (consp (car al))
                 (alist-consp (car al))
                 (alist-p (cdr al))))
    ///
    (more-returns
     (ok (implies ok (alistp al))
         :name alist-p-implies-alistp
         :hints(("Goal" :in-theory (enable alist-p))))))

  (defthm assoc-of-bogus-key
    (implies (and (alist-p al) (not (alist-key-p k)))
                   (not (assoc-equal k al)))
    :hints(("Goal" :in-theory (enable alist-p alist-consp)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection arrays
  (define array-val-p (x)
    :guard t
    :returns (ok booleanp)
    (or (null x)
	(and (consp x)
	     (alist-key-p (car x))
	     (alist-val-p (cdr x)))))

    (define array-val-default ()
      :guard t
      :enabled t
      :returns (def array-val-p :hints(("Goal" :in-theory (enable array-val-p))))
      nil)

  (encapsulate ;; generic properties of arrays
    (((array-p *) => *)
     ((array-init) => *)
     ((array-store * * *) => *)
     ((array-select * *) => *))

    ;; We need to make our function definitions for array-p, array-init
    ;;   array-store, and array-select local, but the constraints (i.e.
    ;;   theorems) about them need to be exported from the encapsulation.
    ;;   I wrote the local definitions first, and then the exported
    ;;   more-returns theorems.
    (local (define array-p (ar)
             :guard t
             :returns (ok any-p)
             (if (null ar) t
                 (and (consp ar)
                      (consp (car ar))
                      (alist-key-p (caar ar))
                      (array-val-p (cdar ar))
                      (array-p (cdr ar))))
             ///
             (more-returns
              (ok (implies ok (alistp ar))
                        :name array-p--implies--alistp
                        :hints(("Goal" :in-theory (enable array-p)))))))
    (more-returns array-p
     (ok (booleanp ok) :name booleanp-of-array-p
         :hints(("Goal" :in-theory (enable array-p)))))

    (local (define array-init ()
             :guard t
             :returns (ar any-p)
             nil))

    (local (define array-store ((k alist-key-p) (v array-val-p) (ar0 array-p))
             :returns (ar any-p)
             (if (and (alist-key-p k) (array-val-p v) (array-p ar0))
                 (acons k v ar0)
               nil)))

    (local (define array-select ((k alist-key-p) (ar array-p))
             :returns (v any-p)
             :guard-hints(("Goal"
                           :do-not-induct t
                           :in-theory (disable array-p--implies--alistp)
                           :use((:instance array-p--implies--alistp (ar ar)))))
             (if (and (alist-key-p k) (array-p ar) (assoc-equal k ar))
                 (cdr (assoc-equal k ar))
               (array-val-default))))

    ;; I'll be lazy and just enable all of local functions for arrays
    ;;   before proving their simple properties.
    (local (in-theory (enable array-p array-init array-store array-select)))

    (local (defthmd array-assoc-p-of-assoc-equal
             (implies (and (alist-key-p k) (array-p ar))
                      (or (null (assoc-equal k ar))
                          (and (alist-key-p (car (assoc-equal k ar)))
                               (array-val-p (cdr (assoc-equal k ar))))))
             :hints(("Goal" :in-theory (enable (array-p))))))

    (more-returns array-init
                  (ar (array-p ar) :name array-p-of-array-init))

    (more-returns array-store
                  (ar (array-p ar) :name array-p-of-array-store))

    (more-returns array-select
                  (v (array-val-p v)
                     :name array-val-p-of-array-select
                     :hints(
		      ("Goal"
		       :in-theory (enable array-p)
		       :use((:instance array-assoc-p-of-assoc-equal (k k) (ar ar))))
		      ("Subgoal 6"
		       :expand (hide (array-val-default)))))
                  (v (implies (not (alist-key-p k))
                              (equal v (array-val-default)))
                     :name array-select-of-bogus-key))

    (defthm array-select-of-array-init
      (equal (array-select k (array-init)) (array-val-default)))

    (defthm array-select-of-array-store
      (implies (and (alist-key-p k1) (alist-key-p k0) (array-val-p v0)
                    (array-p ar))
               (equal (array-select k1 (array-store k0 v0 ar))
                      (if (equal k1 k0) v0 (array-select k1 ar)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection equivalence-of-arrays-and-alists
;  (define array-val-assoc-equiv ((array-v array-val-p) (assoc-v alist-assoc-p))
;    :returns (equiv booleanp)
;    :guard-hints(("Goal" :in-theory (enable alist-assoc-p)))
;    :enabled t
;    (and (array-val-p array-v) (alist-assoc-p assoc-v)
;         (or (and (not (array-val->valid array-v)) (null assoc-v))
;                   (and (array-val->valid array-v)
;                              assoc-v
;                              (equal (array-val->value array-v) (cdr assoc-v))))))
;
;  (defthm array-and-alist-match-when-not-alist-key-p
;    (implies 
;     (and (alist-alist-p al) (array-p ar) (not (alist-key-p k)))
;     (array-val-assoc-equiv (array-select k ar) (assoc-equal k al))))
;  (local (in-theory (disable alist-assoc-p)))

  (defun-sk array-alist-equiv (ar al)
    (forall (k)
            (implies (and (array-p ar) (alist-p al) (alist-key-p k))
                     (equal (array-select k ar) (assoc-equal k al)))))

  (defthm array-alist-equiv--bogus-witness-implies-all-match
    (implies
     (and (alist-p al) (array-p ar) (alist-key-p k)
          (equal
           (array-select (array-alist-equiv-witness ar al) ar)
           (assoc-equal  (array-alist-equiv-witness ar al) al)))
     (equal (array-select k ar) (assoc-equal k al)))
    :hints(("Goal"
            :in-theory (disable array-alist-equiv-necc)
            :use((:instance array-alist-equiv-necc (ar ar) (al al) (k k))))))

  (defthm equiv-of-array-alist-store
    (implies (and (array-p ar) (alist-p al)
                  (alist-key-p k) (alist-val-p v)
                  (array-alist-equiv ar al))
	     (array-alist-equiv (array-store k (cons k v) ar)
                                (acons k v al)))
    :hints(("Goal"
            :in-theory (e/d (array-val-p) (array-alist-equiv-necc array-select-of-array-store))
            :use(
                 (:instance array-alist-equiv-necc (ar ar) (al al)
                                  (k (array-alist-equiv-witness (array-store k (cons k v) ar)
                                                                (acons k v al))))
                 (:instance array-select-of-array-store (ar ar) (k0 k) (k1 k) (v0 (cons k v)))
                 (:instance array-select-of-array-store (ar ar) (k0 k) (v0 (cons k v))
                            (k1 (array-alist-equiv-witness (array-store k (cons k v) ar)
							   (acons k v al)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection translation
  ;; Note: the proofs in this section are all straightforward -- they build
  ;;   on results from the previous two sections in "obvious" ways.  None of
  ;;   these proofs use induction.  When debugging these proofs I (mrg) often
  ;;   found it helpful to add a
  ;;     :do-non-induct t
  ;;   hint.  That way, when I missed enabling a function or instantiating a
  ;;   theorem, ACL2 fails with relatively easy easy to debug subgoals.  If
  ;;   ACL2 goes wild with induction, the proof debugging is harder (for me).
  (defthm translation-of-nil
    (array-alist-equiv (array-init) nil))

  (defthm translation-of-acons
    (implies
     (and (array-p ar) (alist-p al) (alist-key-p k)
          (alist-val-p v) (array-alist-equiv ar al))
     (array-alist-equiv (array-store k (cons k v) ar)
                        (acons k v al)))
    :hints(("Goal"
            :in-theory (disable equiv-of-array-alist-store)
            :use((:instance equiv-of-array-alist-store (ar ar) (al al) (k k) (v v))))))

  (defthm translation-of-assoc-equal
    (implies (and (array-p ar) (alist-p al) (alist-key-p k)
                              (array-alist-equiv ar al))
                   (equal (array-select k ar) (assoc-equal k al)))
    :hints(("Goal"
            :do-not-induct t
            :in-theory (disable array-alist-equiv--bogus-witness-implies-all-match)
            :use((:instance array-alist-equiv--bogus-witness-implies-all-match
                            (ar ar) (al al) (k k))))))
)

