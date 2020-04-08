;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "../utils/pseudo-term")
(include-book "path-cond")
(include-book "term-substitution")
;; (include-book "evaluator")

;; reduce not's in term
(define simple-transformer ((term pseudo-termp))
  :returns (new-term pseudo-termp)
  (b* ((term (pseudo-term-fix term))
       (new-term
        (case-match term
          (('not ('not term1)) term1)
          (& term))))
    new-term))

(defsection |these-theorems-should-move-to-../utils/pseudo-term|
  ;; mrg:  I needed these for some of the theorems that I added.
  (defthm consp-of-pseudo-term-list-fix
    (implies (consp x)
             (consp (pseudo-term-list-fix x)))
    :hints(("Goal" :expand (pseudo-term-list-fix x))))

  (defthm null-of-pseudo-term-list-fix
    (implies (not (consp x))
             (equal (pseudo-term-list-fix x) nil))
    :hints(("Goal" :expand (pseudo-term-list-fix x))))

  (defthm len-of-pseudo-term-list-fix
    (equal (len (pseudo-term-list-fix x))
           (len x))
    :hints(("Goal" :in-theory (enable pseudo-term-list-fix)))))

(defsection |maybe-I-want-to-change-the-definition-of-is-conjunct?|
  ;; I suspect that reasoning about is-conjunct? will be easier with
  ;; the property below.  We could probably modify is-conjunct? to
  ;; test (equal (cddddr term) nil) instead of (equal (len term) 4).
  ;; That would be changing two lines of code instead of proving
  ;; four theorems.
  (local (defthm lemma-1
           (implies (equal (len term) 4)
                    (not (consp (cddddr term))))
           :hints(("Goal"
                   :in-theory (disable len)
                   :expand ((len term)
                            (len (cdr term))
                            (len (cdr (cdr term)))
                            (len (cdr (cdr (cdr term))))
                            (len (cdr (cdr (cdr (cdr term))))))))))

  (defthm cddddr-when-is-conjunct?
    (implies (is-conjunct? term)
             (not (consp (cddddr term))))
    :hints(
           ("Goal"
            :in-theory (disable len pseudo-termp lemma-1)
            :use((:instance lemma-1))
            :expand(
                    (is-conjunct? term)
                    (pseudo-term-fix term))))))

(defsection typed-term
  (local (in-theory (disable pseudo-termp)))

  (defprod typed-term
    ((term pseudo-termp :default ''nil)
     (path-cond pseudo-termp :default ''t)
     (judgements pseudo-termp :default '(if (if (symbolp 'nil)
                                                (if (booleanp 'nil) 't 'nil)
                                              'nil)
                                            't
                                          'nil))))

  (deflist typed-term-list
    :elt-type typed-term-p
    :true-listp t)

  (define typed-term-list->term-lst ((tterm-lst typed-term-list-p))
    :measure (len (typed-term-list-fix tterm-lst))
    :returns (term-lst pseudo-term-listp)
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((unless (consp tterm-lst)) nil)
         ((cons tterm-hd tterm-tl) tterm-lst)
         ((typed-term tth) tterm-hd))
      (cons tth.term (typed-term-list->term-lst tterm-tl)))
    ///
    (more-returns
     (term-lst
      (equal (acl2-count
              (typed-term-list->term-lst (typed-term-list-fix tterm-lst)))
             (acl2-count term-lst))
      :name acl2-count-equal-of-typed-term-list-fix
      :hints (("Goal"
               :expand (typed-term-list->term-lst tterm-lst))))
     (term-lst
      (implies (consp tterm-lst)
               (< (acl2-count (typed-term->term (car tterm-lst)))
                  (acl2-count term-lst)))
      :name acl2-count-of-car-of-typed-term-list-p)
     (term-lst
      (implies (typed-term-list-p tterm-lst)
               (equal (len term-lst) (len tterm-lst)))
      :name typed-term-list->term-lst-maintains-len)
     ;; added by mrg
     (term-lst (implies (consp tterm-lst) (consp term-lst))
               :name consp-of-typed-term-lst->term-lst
               :hints(("Goal" :in-theory (enable typed-term-list->term-lst))))
     (term-lst (implies (not (consp tterm-lst)) (equal term-lst nil))
               :name null-of-typed-term-lst->term-lst
               :hints(("Goal" :in-theory (enable typed-term-list->term-lst))))))

  (defthm acl2-count-of-cdr-of-typed-term-list-p
    (implies (consp tterm-lst)
             (< (acl2-count (typed-term-list->term-lst (cdr tterm-lst)))
                (acl2-count (typed-term-list->term-lst tterm-lst))))
    :hints (("Goal"
             :expand (typed-term-list->term-lst tterm-lst))))

  (define typed-term-list->judgements ((tterm-lst typed-term-list-p))
    :measure (len (typed-term-list-fix tterm-lst))
    :returns (judges pseudo-termp)
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((unless (consp tterm-lst)) ''t)
         ((cons tterm-hd tterm-tl) tterm-lst)
         ((typed-term tth) tterm-hd))
      `(if ,tth.judgements
           ,(typed-term-list->judgements tterm-tl)
         'nil)))

  ;; mrg:  I removed the check for uniform-path-cond? because it
  ;;   was forcing messy induction proofs when reasoning about
  ;;   make-typed-term-list.  I suspect that this simpler version
  ;;   typed-term-list->path-cond "works" for everything we need
  ;;   anyway.
  ;;     Then, I moved the definition of typed-term-list->path-cond
  ;;   *before* uniform-path-cond? so I could use it in the definition
  ;;   of uniform-path-cond?.  This makes subsequent proofs work
  ;;   with fewer hints.
  (define typed-term-list->path-cond ((tterm-lst typed-term-list-p))
    :returns (path-cond pseudo-termp)
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((unless (consp tterm-lst)) ''t)
         ((cons tterm-hd &) tterm-lst)
         ((typed-term tth) tterm-hd))
      tth.path-cond))

  ;; mrg:  added uniform-path-help because it makes reasoning about
  ;;   uniform-path-cond? easier.  That's because uniform-path-help
  ;;   has a "better" induction schema (by keeping path-cond unchanged).
  (define uniform-path-help ((tterm-lst typed-term-list-p) (path-cond pseudo-termp))
    :returns (ok booleanp)
    (b* (((unless (consp tterm-lst)) t)
         ((unless (equal (typed-term-list->path-cond tterm-lst) path-cond)) nil))
      (uniform-path-help (cdr tterm-lst) path-cond))
    ///
    (more-returns
     (ok (implies (not (consp tterm-lst)) ok)
         :name uniform-path-help-of-atom)
     (ok (implies ok (uniform-path-help (cdr tterm-lst) path-cond))
         :name uniform-path-help-of-cdr
         :hints(("Goal" :in-theory (enable uniform-path-help))))
     (ok (implies (and ok (consp (cdr tterm-lst)))
                  (and (equal (typed-term-list->path-cond (cdr tterm-lst)) path-cond)
                       (equal (typed-term-list->path-cond tterm-lst) path-cond)))
         :name uniform-path-help-when-len-geq-2
         :hints(("Goal" :in-theory (enable uniform-path-help))))))

  (define uniform-path-cond? ((tterm-lst typed-term-list-p))
    :returns (ok booleanp)
    (uniform-path-help tterm-lst (typed-term-list->path-cond tterm-lst))
    ///
    (more-returns
     (ok (implies ok (uniform-path-cond? (cdr tterm-lst)))
         :name uniform-path-cond?-of-cdr
         :hints(("Goal" :cases(
                               (and (consp tterm-lst) (consp (cdr tterm-lst)))
                               (and (consp tterm-lst) (not (consp (cdr tterm-lst))))))))
     (ok (implies (and (typed-term-list-p tterm-lst)
                       (consp tterm-lst) (consp (cdr tterm-lst))
                       ok)
                  (equal (typed-term-list->path-cond (cdr tterm-lst))
                         (typed-term-list->path-cond tterm-lst)))
         :name equal-of-uniform-path-cond?)))


  ;; make-typed-term-list-guard -- state the relationship that
  ;; make-typed-term-list needs between term-lst and judges.
  ;; By moving this into the guard, the body of make-typed-term-list
  ;; doesn't need a bunch of ((if bad) (er ?hard ...)) bindings in its b*.
  ;; That makes reasoning about make-typed-term-list easier.
  (define make-typed-term-list-guard ((term-lst pseudo-term-listp)
                                      (path-cond pseudo-termp)
                                      (judges pseudo-termp))
    :returns (ok booleanp)
    :enabled t
    (b* (((unless (pseudo-term-listp term-lst)) nil)
         ((unless (pseudo-termp path-cond)) nil)
         ((unless (pseudo-termp judges)) nil)
         ((unless (is-conjunct? judges)) nil)
         ((if (and (null term-lst) (equal judges ''t))) t)
         ((if (or  (null term-lst) (equal judges ''t))) nil)
         (term-tl (cdr term-lst))
         ((list & & judge-tl &) judges)) ;; (if judge-hd judge-tl nil)
      (make-typed-term-list-guard term-tl path-cond judge-tl))
    ///
    (more-returns
     (ok (implies (and ok (consp term-lst))
                  (make-typed-term-list-guard (cdr term-lst) path-cond (caddr judges)))
         :name make-typed-term-list-guard-of-cdr
         :hints(("Goal" :in-theory (enable make-typed-term-list-guard))))))

  ;; make-typed-term-list-fix-judges
  ;;   A "fixing" function to make judges satisfy make-typed-term-list-guard.
  ;;   Takes about 20 seconds to define this function (2.6GHz, i5 Macbook Pro).
  ;;   The main culprit is the more-returns theorem
  ;;     make-typed-term-list-guard-of-make-typed-term-list-fix-judges
  (define make-typed-term-list-fix-judges ((term-lst pseudo-term-listp)
                                           (path-cond pseudo-termp)
                                           (judges pseudo-termp))
    :guard (make-typed-term-list-guard term-lst path-cond judges)
    :returns (j-fix pseudo-termp)
    :verify-guards nil
    (mbe
     :logic
     (b* ((term-lst (pseudo-term-list-fix term-lst))
          (path-cond (pseudo-term-fix path-cond))
          (judges (pseudo-term-fix judges))
          ((if (null term-lst)) ''t)
          ((mv judge-hd judge-tl)
           (if (and (is-conjunct? judges) (not (equal judges ''t)))
               (mv (cadr judges) (caddr judges))
             (mv ''t ''t)))
          (jtl-fix (make-typed-term-list-fix-judges (cdr term-lst)
                                                    path-cond
                                                    judge-tl)))
       `(if ,judge-hd ,jtl-fix 'nil))
     :exec judges)
    ///
    ;; mrg:  the proof of idempotence-of-make-typed-term-list-fix-judges
    ;;   fails when stated as a more-returns theorem but succeeds ;   this way
    (defthm idempotence-of-make-typed-term-list-fix-judges
      (let ((j-fix (make-typed-term-list-fix-judges tterm-lst path-cond judges)))
        (equal (make-typed-term-list-fix-judges tterm-lst path-cond j-fix) j-fix))
      :hints(("Goal"
              :in-theory (e/d (make-typed-term-list-fix-judges) (pseudo-termp)))))
    (more-returns
     (j-fix (make-typed-term-list-guard (pseudo-term-list-fix term-lst)
                                        (pseudo-term-fix path-cond)
                                        j-fix)
            :name
            make-typed-term-list-guard-of-make-typed-term-list-fix-judges)
     ;; make-typed-term-list-judges-fix-when-make-typed-term-list-guard
     ;; takes about 15 seconds to prove -- even if I give it a shorter name.
     ;; That's kind of annoying.  Might want to figure out why (i.e. why it
     ;; takes so long.  I know why waiting for the proof to finish is
     ;; annoying)
     ;; Yan: I disabled some rules, not it runs slightly faster
     (j-fix (implies (make-typed-term-list-guard term-lst path-cond judges)
                     (equal j-fix judges))
            :name make-typed-term-list-judges-fix-when-make-typed-term-list-guard
            :hints(("Goal" :in-theory (e/d (is-conjunct?
                                            make-typed-term-list-fix-judges)
                                           (symbol-listp
                                            acl2::symbolp-of-car-when-symbol-listp
                                            acl2::symbol-listp-of-cdr-when-symbol-listp))))))
    (verify-guards make-typed-term-list-fix-judges
      :hints(("Goal"
              :in-theory (disable make-typed-term-list-judges-fix-when-make-typed-term-list-guard)
              :use((:instance
                    make-typed-term-list-judges-fix-when-make-typed-term-list-guard)))))
    )


  (define make-typed-term-list ((term-lst pseudo-term-listp)
                                (path-cond pseudo-termp)
                                (judges pseudo-termp))
    :guard (make-typed-term-list-guard term-lst path-cond judges)
    :returns (tterm-lst typed-term-list-p)
    :guard-hints(("Goal"
                  :expand ((make-typed-term-list-guard term-lst path-cond judges))))

    (b* ((term-lst (pseudo-term-list-fix term-lst))
         (path-cond (pseudo-term-fix path-cond))
         (judges (make-typed-term-list-fix-judges term-lst path-cond judges))
         ((unless (consp term-lst)) nil)
         ((cons term-hd term-tl) term-lst)
         ((list & judge-hd judge-tl &) judges))
      (cons (make-typed-term :term term-hd :path-cond path-cond
                             :judgements judge-hd)
            (make-typed-term-list term-tl path-cond judge-tl)))
    ///
    ;; mrg: first, two lemmas about make-typed-term-list-fix-judges that
    ;;   are needed for the proof of
    ;;   typed-term-list->judgements-of-make-typed-term-list
    (local (defthm lemma-j1
             (implies (or (not (consp term-lst)) (not (consp (pseudo-term-list-fix term-lst))))
                      (equal (make-typed-term-list-fix-judges term-lst path-cond judges)
                             ''t))
             :hints(("Goal" :expand((make-typed-term-list-fix-judges term-lst path-cond judges))))))


    ;; mrg: lemma-j2 is a "cut-and-paste" lemma from a failed subgoal for
    ;;   typed-term-list->judgements-of-make-typed-term-list.  The proof
    ;;   feels a bit brittle.  See the comments in the theorem statement.
    (local (defthm lemma-j2
             (implies
              ;; the writer doesn't find lemma-j2 if the hypothesis is (consp term-lst)
              (consp (pseudo-term-list-fix term-lst))
              ;; The proof of typed-term-list->judgements-of-make-typed-term-list fails
              ;; with a rewrite loop if I don't use this (equal ... t) construction.
              (equal
               (equal (make-typed-term-list-fix-judges term-lst path-cond judges)
                      (LIST
                       'IF
                       (PSEUDO-TERM-FIX
                        (CADR (MAKE-TYPED-TERM-LIST-FIX-JUDGES (PSEUDO-TERM-LIST-FIX TERM-LST)
                                                               (PSEUDO-TERM-FIX PATH-COND)
                                                               JUDGES)))
                       (MAKE-TYPED-TERM-LIST-FIX-JUDGES
                        (CDR (PSEUDO-TERM-LIST-FIX TERM-LST))
                        (PSEUDO-TERM-FIX PATH-COND)
                        (CADDR (MAKE-TYPED-TERM-LIST-FIX-JUDGES (PSEUDO-TERM-LIST-FIX TERM-LST)
                                                                (PSEUDO-TERM-FIX PATH-COND)
                                                                JUDGES)))
                       ''nil))
               t))
             :hints(("Goal"
                     :expand(
                             (make-typed-term-list-fix-judges term-lst path-cond judges)
                             (MAKE-TYPED-TERM-LIST-FIX-JUDGES (PSEUDO-TERM-LIST-FIX TERM-LST)
                                                              (PSEUDO-TERM-FIX PATH-COND)
                                                              JUDGES))))))

    (more-returns
     ;; mrg: I changed acl2-count-of-typed-term-list->term-lst into a
     ;;   more-returns theorem (it had been a defthm) for consistency
     ;;   Note: we could also prove
     ;;     (equal (len (make-typed-term-list term-lst path-cond judges))
     ;;            (len term-lst))
     ;;   If that would be useful in subsequent measure proofs.
     (tterm-lst (<= (acl2-count (typed-term-list->term-lst tterm-lst))
                    (acl2-count term-lst))
                :name acl2-count-of-typed-term-list->term-lst
                :hints(("Goal" :in-theory (enable typed-term-list->term-lst)))
                :rule-classes :linear)
     ;; mrg: I added the more-returns theorems from here to the end of
     ;;      define make-typed-term-list.
     (tterm-lst (implies (consp term-lst) (consp tterm-lst))
                :name consp-of-make-typed-term-list
                :hints(("Goal"
                        :expand((make-typed-term-list term-lst path-cond judges)))))

     (tterm-lst (implies (not (consp term-lst)) (equal tterm-lst nil))
                :name null-of-make-typed-term-list
                :hints(("Goal"
                        :expand((make-typed-term-list term-lst path-cond judges)))))

     (tterm-lst (implies (pseudo-term-listp term-lst)
                         (equal (typed-term-list->term-lst tterm-lst) term-lst))
                :name typed-term-list->term-lst-of-make-typed-term-list
                :hints(("Goal" :in-theory (enable typed-term-list->term-lst))))

     (tterm-lst (equal (typed-term-list->path-cond tterm-lst)
                       (if (consp term-lst) (pseudo-term-fix path-cond) ''t))
                :name typed-term-list->path-cond-of-make-typed-term-list
                :hints(("Goal"
                        :in-theory (enable typed-term-list->path-cond))))

     (tterm-lst (equal (typed-term-list->judgements tterm-lst)
                       (make-typed-term-list-fix-judges term-lst path-cond judges))
                :name typed-term-list->judgements-of-make-typed-term-list
                :hints(("Goal" :in-theory (enable typed-term-list->judgements))))

     (tterm-lst (implies (pseudo-termp path-cond)
                         (uniform-path-help tterm-lst path-cond))
                :name uniform-path-help-of-make-typed-term-list
                :hints(("Goal"
                        :in-theory (enable uniform-path-help
                                           make-typed-term-list
                                           typed-term-list->path-cond))))

     (tterm-lst (implies (pseudo-termp path-cond)
                         (uniform-path-cond? tterm-lst))
                :name uniform-path-cond?-of-make-typed-term-list
                :hints(("Goal" :in-theory (enable uniform-path-cond?)))))))


(defsection make-typed-term-list-from-fields
  ;; mrg: my goal is to show that if tterm-lst is a typed-term-list-p
  ;;   and tterm-list satisfies uniform-path-cond?, then 
  ;;     (equal
  ;;       (make-typed-term-list
  ;;         (typed-term-list->term-lst tterm-lst)
  ;;         (typed-term-list->path-cond tterm-lst)
  ;;         (typed-term-list->judgements tterm-lst))
  ;;     tterm-lst)
  ;;   This is theorem make-typed-term-list-from-fields.
  ;;   
  ;;   Along the way, I prove a few other theorems that may be useful
  ;;   outside of this defsection:
  ;;     make-typed-term-list-guard-from-fields
  ;;       this theorem states that make-typed-term-list-guard is
  ;;       satisfied by
  ;;         (typed-term-list->term-lst tterm-lst)
  ;;         (typed-term-list->path-cond tterm-lst)
  ;;         (typed-term-list->judgements tterm-lst)
  ;;       no matter what tterm-lst is.  Aha, that's why I made the
  ;;       the changes that I did to those functions for the cases
  ;;       where tterm-lst is "bad".
  ;;
  ;;     car-of-make-typed-term-list
  ;;       If tterm-list is a non-nil typed-term-list-p, then
  ;;         (equal
  ;;           (car (make-typed-term-list
  ;;                 (typed-term-list->term-lst tterm-lst)
  ;;                 (typed-term-list->path-cond tterm-lst)
  ;;                 (typed-term-list->judgements tterm-lst)))
  ;;           (car tterm-lst))
  ;;       I don't need the uniform-path-cond? hypthesis here.

  (local (in-theory (disable pseudo-termp)))
  
  (local (defthm lemma-1
           (implies (pseudo-termp path-cond)
                    (make-typed-term-list-guard
                     (typed-term-list->term-lst tterm-lst)
                     path-cond
                     (typed-term-list->judgements tterm-lst)))
           :hints(("Goal"
                   :in-theory (enable
                               make-typed-term-list-guard
                               typed-term-list->term-lst
                               typed-term-list->judgements)))))

  (defthm make-typed-term-list-guard-from-fields
    (make-typed-term-list-guard
     (typed-term-list->term-lst tterm-lst)
     (typed-term-list->path-cond tterm-lst)
     (typed-term-list->judgements tterm-lst)))

  ;; I don't want to enable typed-term-list->judgements for the
  ;; proof of car-of-make-typed-term-list because it makes the
  ;; terms for the :expand hint much messier.
  (local (defthm lemma-2
           (implies
            (and (typed-term-list-p tterm-lst) (consp tterm-lst))
            (and (equal (cadr (typed-term-list->judgements tterm-lst))
                        (typed-term->judgements (car tterm-lst)))
                 (equal (caddr (typed-term-list->judgements tterm-lst))
                        (typed-term-list->judgements (cdr tterm-lst)))))
           :hints(("Goal" :in-theory (enable typed-term-list->judgements)))))

  (defthm car-of-make-typed-term-list
    (let ((tterm-lst2 (make-typed-term-list (typed-term-list->term-lst tterm-lst)
                                            (typed-term-list->path-cond tterm-lst)
                                            (typed-term-list->judgements tterm-lst))))
      (implies (and (typed-term-list-p tterm-lst) (consp tterm-lst))
               (equal (car tterm-lst2)(car tterm-lst))))
    :hints(("Goal"
            :in-theory (disable make-typed-term-list-guard-from-fields)
            :use((:instance make-typed-term-list-guard-from-fields))
            :expand(
                    (typed-term-list->term-lst tterm-lst)
                    (typed-term-list->path-cond tterm-lst)
                    (make-typed-term-list
                     (cons (typed-term->term (car tterm-lst))
                           (typed-term-list->term-lst (cdr tterm-lst)))
                     (typed-term->path-cond (car tterm-lst))
                     (typed-term-list->judgements tterm-lst))))))

  (local (defthmd lemma-3
           (implies (and (typed-term-list-p tterm-lst)
                         (uniform-path-help tterm-lst path-cond)
                         (pseudo-termp path-cond))
                    (let* ((term-lst1  (typed-term-list->term-lst tterm-lst))
                           (judges1    (typed-term-list->judgements tterm-lst))
                           (tterm-lst1 (make-typed-term-list term-lst1 path-cond judges1))
                           (term-lst2  (typed-term-list->term-lst (cdr tterm-lst)))
                           (judges2    (typed-term-list->judgements (cdr tterm-lst)))
                           (tterm-lst2 (make-typed-term-list term-lst2 path-cond judges2)))
                      (equal tterm-lst2 (cdr tterm-lst1))))
           :hints(("Goal"
                   :in-theory (disable lemma-1)
                   :use((:instance lemma-1))
                   :expand(
                           (typed-term-list->term-lst tterm-lst)
                           (typed-term-list->path-cond tterm-lst)
                           (typed-term-list->judgements tterm-lst)
                           (make-typed-term-list
                            (cons (typed-term->term (car tterm-lst))
                                  (typed-term-list->term-lst (cdr tterm-lst)))
                            path-cond
                            (list* 'if
                                   (typed-term->judgements (car tterm-lst))
                                   (typed-term-list->judgements (cdr tterm-lst))
                                   '('nil))))))))

  (local (defthm crock-pain-0
           (implies
            (UNIFORM-PATH-HELP TTERM-LST (TYPED-TERM-LIST->PATH-COND TTERM-LST))
            (equal (MAKE-TYPED-TERM-LIST (TYPED-TERM-LIST->TERM-LST (CDR TTERM-LST))
                                         (TYPED-TERM-LIST->PATH-COND TTERM-LST)
                                         (TYPED-TERM-LIST->JUDGEMENTS (CDR TTERM-LST)))
                   (MAKE-TYPED-TERM-LIST (TYPED-TERM-LIST->TERM-LST (CDR TTERM-LST))
                                         (TYPED-TERM-LIST->PATH-COND (cdr TTERM-LST))
                                         (TYPED-TERM-LIST->JUDGEMENTS (CDR TTERM-LST)))))
           :hints(("Goal"
                   :cases((and (consp tterm-lst) (consp (cdr tterm-lst)))
                          (and (consp tterm-lst) (not (consp (cdr tterm-lst)))))))))

  (local (defthm crock-pain-1
           (let ((tterm-lst2 (MAKE-TYPED-TERM-LIST (TYPED-TERM-LIST->TERM-LST TTERM-LST)
                                                   (TYPED-TERM-LIST->PATH-COND TTERM-LST)
                                                   (TYPED-TERM-LIST->JUDGEMENTS TTERM-LST))))
             (IMPLIES
              (and (EQUAL (MAKE-TYPED-TERM-LIST (TYPED-TERM-LIST->TERM-LST (CDR TTERM-LST))
                                                (TYPED-TERM-LIST->PATH-COND (cdr TTERM-LST))
                                                (TYPED-TERM-LIST->JUDGEMENTS (CDR TTERM-LST)))
                          (CDR TTERM-LST))
                   (TYPED-TERM-LIST-P TTERM-LST)
                   (UNIFORM-PATH-HELP TTERM-LST (TYPED-TERM-LIST->PATH-COND TTERM-LST)))
              (EQUAL (cdr tterm-lst2) (cdr TTERM-LST))))
           :hints(
                  ("Goal"
                   :in-theory (disable lemma-3)
                   :use(
                        (:instance lemma-3 (path-cond (typed-term-list->path-cond tterm-lst))))))))

  (local (defthmd crock-pain-2
           (let ((tterm-lst2 (MAKE-TYPED-TERM-LIST (TYPED-TERM-LIST->TERM-LST TTERM-LST)
                                                   (TYPED-TERM-LIST->PATH-COND TTERM-LST)
                                                   (TYPED-TERM-LIST->JUDGEMENTS TTERM-LST))))
             (implies
              (and (typed-term-list-p tterm-lst) (consp tterm-lst) (consp tterm-lst2)
                   (EQUAL (car tterm-lst2) (car tterm-lst))
                   (EQUAL (cdr tterm-lst2) (cdr tterm-lst)))
              (EQUAL tterm-lst2 tterm-lst)))
           :hints(("Goal"
                   :in-theory (disable car-of-make-typed-term-list consp-of-make-typed-term-list)))))

  (local (defthm crock-pain-3
           (let ((tterm-lst2 (MAKE-TYPED-TERM-LIST (TYPED-TERM-LIST->TERM-LST TTERM-LST)
                                                   (TYPED-TERM-LIST->PATH-COND TTERM-LST)
                                                   (TYPED-TERM-LIST->JUDGEMENTS TTERM-LST))))
             (implies
              (and (typed-term-list-p tterm-lst)
                   (EQUAL (cdr tterm-lst2) (cdr tterm-lst)))
              (equal tterm-lst2 tterm-lst)))
           :hints(("Goal" :use((:instance crock-pain-2))))))

  (local (defthm crock-pain-4
           (let ((tterm-lst2 (MAKE-TYPED-TERM-LIST (TYPED-TERM-LIST->TERM-LST TTERM-LST)
                                                   (TYPED-TERM-LIST->PATH-COND TTERM-LST)
                                                   (TYPED-TERM-LIST->JUDGEMENTS TTERM-LST))))
             (implies
              (and (EQUAL (MAKE-TYPED-TERM-LIST (TYPED-TERM-LIST->TERM-LST (CDR TTERM-LST))
                                                (TYPED-TERM-LIST->PATH-COND (cdr TTERM-LST))
                                                (TYPED-TERM-LIST->JUDGEMENTS (CDR TTERM-LST)))
                          (CDR TTERM-LST))
                   (TYPED-TERM-LIST-P TTERM-LST)
                   (UNIFORM-PATH-HELP TTERM-LST (TYPED-TERM-LIST->PATH-COND TTERM-LST)))
              (equal tterm-lst2 tterm-lst)))))

  (defthm make-typed-term-list-from-fields
    (implies (and (typed-term-list-p tterm-lst)
                  (uniform-path-cond?  tterm-lst))
             (let* ((term-lst (typed-term-list->term-lst tterm-lst))
                    (path-cond (typed-term-list->path-cond tterm-lst))
                    (judges   (typed-term-list->judgements tterm-lst))
                    (tterm-lst2 (make-typed-term-list term-lst path-cond judges)))
               (equal tterm-lst2 tterm-lst)))
    :hints(("Goal"
            :in-theory (e/d (make-typed-term-list uniform-path-cond? uniform-path-help)
                            (crock-pain-0 crock-pain-1 crock-pain-2 crock-pain-3))))))

(defsection make-typed-term-list-fix-judges-when-term-lst-equal-len
  ;; Another bunch of theorems to prove something that I intend to use later
  ;; in this file.
  ;;   (make-typed-term-list-fix-judges term-lst path-cond judges)
  ;; is mostly concerned about judges.  There needs to be a correspondence
  ;; between the conjuncts in judges and the terms in term-lst, but this
  ;; means that the only thing that matters about term-lst is its length.
  ;; Thus, we prove the congruence:
  ;;   (implies (equal (len term-lst) (len term-lst-equiv))
  ;;            (equal (make-typed-term-list-fix-judges term-lst path-cond judges)
  ;;                   (make-typed-term-list-fix-judges term-lst-equiv path-cond judges)))
  ;; We also introduce:
  ;;   equal-len: an equivalence relation we need to state the main congruence.
  ;;   equal-len-implies-equal-len-cdr-1:  a congruence, i.e. cdr preserves equal-len
  ;;   equal-len-implies-equal-len-pseudo-term-list-fix-1:
  ;;     same as len-of-pseudo-term-list-fix but stated as a congruence
  ;;   equal-len-implies-iff-pseudo-term-list-fix-1:
  ;;     same as null-of-pseudo-term-list-fix but stated as a congruence

  (local (in-theory (disable pseudo-termp)))

  (define equal-len (x y)
    :enabled t
    (equal (len x) (len y))
    ///
    (defequiv equal-len))

  (defthm equal-len-of-pseudo-term-list-fix
    (equal-len (pseudo-term-list-fix term-lst) term-lst))

  (defcong equal-len iff (pseudo-term-list-fix term-lst) 1
    :hints(("Goal"
            :expand ((pseudo-term-list-fix term-lst)
                     (pseudo-term-list-fix term-lst-equiv)))))

  (defcong equal-len equal-len (cdr x) 1)
  
  (in-theory (disable equal-len))
  (defcong equal-len equal
    (make-typed-term-list-fix-judges term-lst path-cond judges) 1
    :hints(("Goal" :in-theory (enable make-typed-term-list-fix-judges)))))

;; ---------------------------------------------
;;       Recognizers

(local
 (defthm type-of-0-input-fn
   (implies (and (symbolp fn)
                 (not (equal fn 'quote)))
            (and (not (pseudo-lambdap `(,fn)))
                 (pseudo-termp `(,fn))))
   :hints (("Goal"
            :in-theory (enable pseudo-lambdap)))))

(define typed-term->kind ((tterm typed-term-p))
  :returns (kind symbolp)
  (b* ((tterm (typed-term-fix tterm))
       ((typed-term tt) tterm)
       ((if (acl2::variablep tt.term)) 'variablep)
       ((if (acl2::quotep tt.term)) 'quotep)
       ((cons fn &) tt.term)
       ((if (pseudo-lambdap fn)) 'lambdap)
       ((if (equal fn 'if)) 'ifp))
    'fncallp)
  ///
  (more-returns
   (kind (member-equal kind '(variablep quotep lambdap ifp fncallp))
         :name range-of-typed-term->kind)
   (kind (implies (and (typed-term-p tterm)
                       (not (equal kind 'variablep))
                       (not (equal kind 'quotep))
                       (not (equal kind 'lambdap))
                       (not (equal kind 'ifp)))
                  (equal kind 'fncallp))
         :name cases-of-typed-term->kind)
   (kind (implies (equal kind 'variablep)
                  (acl2::variablep (typed-term->term tterm)))
         :name implies-of-variable-kind)
   (kind (implies (equal kind 'quotep)
                  (acl2::quotep (typed-term->term tterm)))
         :name implies-of-quote-kind)
   (kind (implies (equal kind 'lambdap)
                  (and (consp (typed-term->term tterm))
                       (pseudo-lambdap (car (typed-term->term tterm)))))
         :name implies-of-lambda-kind)
   (kind (implies (equal kind 'ifp)
                  (and (consp (typed-term->term tterm))
                       (equal (car (typed-term->term tterm)) 'if)))
         :name implies-of-if-kind)
   (kind (implies (equal kind 'fncallp)
                  (and (consp (typed-term->term tterm))
                       (not (equal (car (typed-term->term tterm)) 'quote))
                       (symbolp (car (typed-term->term tterm)))))
         :name implies-of-fncall-kind)
   (kind (implies (equal kind x)
                  (equal (typed-term->kind
                          (typed-term (typed-term->term tterm) a b))
                         x))
         :name kind-preserved)
   (kind (implies (not (equal kind x))
                  (not (equal (typed-term->kind
                               (typed-term (typed-term->term tterm) a b))
                              x)))
         :name not-kind-preserved))
  (defthm good-typed-fncall-of-0-input-fn
    (implies (and (symbolp fn)
                  (not (equal fn 'quote))
                  (not (equal fn 'if))
                  (pseudo-termp path-cond)
                  (pseudo-termp judges))
             (equal (typed-term->kind
                     (typed-term `(,fn) path-cond `(if ,judges 't 'nil)))
                    'fncallp))))

(define good-typed-variable-p ((tterm typed-term-p)
                               (options type-options-p))
  :returns (ok booleanp)
  (b* ((tterm (typed-term-fix tterm))
       (options (type-options-fix options))
       ((typed-term tt) tterm)
       ((type-options to) options))
    ;; (if (is-conjunct-list? tt.judgements tt.term to.supertype) t nil)
    t))

#|
(good-typed-variable-p (typed-term 'x
''t
'(if (if (booleanp (rational-integer-alistp x))
't
'nil)
(if (if 't 't 'nil) 't 'nil)
'nil)))
|#

(define good-typed-quote-p ((tterm typed-term-p)
                            (options type-options-p))
  :returns (ok booleanp)
  (b* ((tterm (typed-term-fix tterm))
       (options (type-options-fix options))
       ((typed-term tt) tterm)
       ((type-options to) options))
    ;; (if (is-conjunct-list? tt.judgements tt.term to.supertype) t nil)
    t))

#|
(good-typed-quote-p (typed-term ''t
''t
'(if (if (symbolp 't)
(if (booleanp 't) 't 'nil)
'nil)
't
'nil)))
|#


;; mrg: I added the test
;;   (make-typed-term-list-guard actuals tt.path-cond actuals-judge)
;; to good-typed-lambda-p and good-typed-fncall-p.
;; This probably creates a verification obligation for the code that
;; creates judgements for lambdas and function calls.
(defines good-typed-term
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :hints (("Goal"
           :in-theory (e/d ()
                           (pseudo-termp
                            pseudo-term-listp
                            equal-fixed-and-x-of-pseudo-termp
                            symbol-listp
                            acl2::pseudo-termp-cadr-from-pseudo-term-listp))))

  (define good-typed-lambda-p ((tterm typed-term-p)
                               (options type-options-p))
    :returns (ok booleanp)
    :guard (and (consp (typed-term->term tterm))
                (pseudo-lambdap (car (typed-term->term tterm))))
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   0)
    :ignore-ok t
    (b* ((tterm (typed-term-fix tterm))
         (options (type-options-fix options))
         ((typed-term tt) tterm)
         ((type-options to) options)
         ((unless (mbt (and (consp tt.term)
                            (pseudo-lambdap (car tt.term)))))
          nil)
         ((cons fn actuals) tt.term)
         (formals (lambda-formals fn))
         (body (lambda-body fn))
         ((unless (consp tt.judgements)) nil)
         (match?
          (case-match tt.judgements
            (('if return-judge
                 ('if (('lambda !formals body-judge) . !actuals)
                     actuals-judge
                   ''nil)
               ''nil)
             (and ;; (is-conjunct-list? return-judge tt.term to.supertype)
              (make-typed-term-list-guard actuals tt.path-cond actuals-judge) ;; added by mrg
              (good-typed-term-list-p
               (make-typed-term-list actuals tt.path-cond actuals-judge)
               to)
              (b* ((shadowed-path-cond
                    (shadow-path-cond formals tt.path-cond))
                   (substed-actuals-judgements
                    (term-substitution actuals-judge
                                       (pairlis$ actuals formals)
                                       t)))
                (good-typed-term-p
                 (make-typed-term :term body
                                  :path-cond `(if ,shadowed-path-cond
                                                  ,substed-actuals-judgements
                                                'nil)
                                  :judgements body-judge)
                 to))))
            (& nil))))
      (if match? t nil)))

  (define good-typed-if-p ((tterm typed-term-p)
                           (options type-options-p))
    :returns (ok booleanp)
    :guard (and (consp (typed-term->term tterm))
                (equal (car (typed-term->term tterm)) 'if))
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   0)
    :ignore-ok t
    (b* ((tterm (typed-term-fix tterm))
         (options (type-options-fix options))
         ((typed-term tt) tterm)
         ((type-options to) options)
         ((unless (mbt (and (consp tt.term)
                            (equal (car tt.term) 'if))))
          nil)
         ((unless (equal (len (cdr tt.term)) 3))
          (er hard? 'typed-term=>good-typed-if-p
              "Malformed if term: ~q0" tt.term))
         ((list & cond then else) tt.term)
         ((unless (consp tt.judgements)) nil)
         (match?
          (case-match tt.judgements
            (('if judge-if-top
                 ('if judge-cond
                     ('if !cond judge-then judge-else)
                   ''nil)
               ''nil)
             (and ;; (is-conjunct-list? judge-if-top tt.term to.supertype)
              (good-typed-term-p
               (make-typed-term :term cond
                                :path-cond tt.path-cond
                                :judgements judge-cond)
               to)
              (good-typed-term-p
               (make-typed-term :term then
                                :path-cond
                                `(if ,(simple-transformer cond)
                                     ,tt.path-cond 'nil)
                                :judgements judge-then)
               to)
              (good-typed-term-p
               (make-typed-term :term else
                                :path-cond
                                `(if ,(simple-transformer `(not ,cond))
                                     ,tt.path-cond 'nil)
                                :judgements judge-else)
               to)))
            (& nil))))
      (if match? t nil)))

  (define good-typed-fncall-p ((tterm typed-term-p)
                               (options type-options-p))
    :returns (ok booleanp)
    :guard (and (consp (typed-term->term tterm))
                (not (equal (car (typed-term->term tterm)) 'quote))
                (symbolp (car (typed-term->term tterm))))
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   0)
    :ignore-ok t
    (b* ((tterm (typed-term-fix tterm))
         (options (type-options-fix options))
         ((typed-term tt) tterm)
         ((type-options to) options)
         ((unless (mbt (consp tt.term))) nil)
         ((cons & actuals) tt.term)
         ((unless (consp tt.judgements)) nil)
         (match?
          (case-match tt.judgements
            (('if return-judge actuals-judge ''nil)
             (and ;; (is-conjunct-list? return-judge tt.term to.supertype)
              (make-typed-term-list-guard actuals tt.path-cond actuals-judge) ;; added by mrg
              (good-typed-term-list-p
               (make-typed-term-list actuals tt.path-cond actuals-judge)
               options)))
            (& nil))))
      (if match? t nil)))

  (define good-typed-term-p ((tterm typed-term-p)
                             (options type-options-p))
    :returns (ok booleanp)
    :measure (list (acl2-count (typed-term->term (typed-term-fix tterm)))
                   1)
    (b* ((tterm (typed-term-fix tterm))
         ((typed-term tt) tterm)
         ((if (equal (typed-term->kind tt) 'variablep))
          (good-typed-variable-p tt options))
         ((if (equal (typed-term->kind tt) 'quotep))
          (good-typed-quote-p tt options))
         ((if (equal (typed-term->kind tt) 'lambdap))
          (good-typed-lambda-p tt options))
         ((if (equal (typed-term->kind tt) 'ifp))
          (good-typed-if-p tt options)))
      (good-typed-fncall-p tt options)))

  (define good-typed-term-list-p ((tterm-lst typed-term-list-p)
                                  (options type-options-p))
    :returns (ok booleanp)
    :measure (list (acl2-count
                    (typed-term-list->term-lst
                     (typed-term-list-fix tterm-lst)))
                   1)
    :hints (("Goal"
             :in-theory (enable typed-term-list->term-lst)))
    (b* ((tterm-lst (typed-term-list-fix tterm-lst))
         ((unless (consp tterm-lst)) t)
         ((cons tterm-hd tterm-tl) tterm-lst))
      (and (good-typed-term-p tterm-hd options)
           (good-typed-term-list-p tterm-tl options)
           (if tterm-tl ;; added by mrg -- ensures good-typed-term-list-p => uniform-path-cond?
               (equal (typed-term->path-cond tterm-hd)
                      (typed-term-list->path-cond tterm-tl))
             t))))
  ///
  (defthm good-typed-variable-p-of-good-term
    (implies (and (typed-term-p tterm)
                  (equal (typed-term->kind tterm) 'variablep))
             (iff (good-typed-term-p tterm options)
                  (good-typed-variable-p tterm options))))
  (defthm good-typed-quote-p-of-good-term
    (implies (and (typed-term-p tterm)
                  (equal (typed-term->kind tterm) 'quotep))
             (iff (good-typed-term-p tterm options)
                  (good-typed-quote-p tterm options))))
  (defthm good-typed-lambda-p-of-good-term
    (implies (and (typed-term-p tterm)
                  (equal (typed-term->kind tterm) 'lambdap))
             (iff (good-typed-term-p tterm options)
                  (good-typed-lambda-p tterm options))))
  (defthm good-typed-if-p-of-good-term
    (implies (and (typed-term-p tterm)
                  (equal (typed-term->kind tterm) 'ifp))
             (iff (good-typed-term-p tterm options)
                  (good-typed-if-p tterm options))))
  (defthm good-typed-fncall-p-of-good-term
    (implies (and (typed-term-p tterm)
                  (equal (typed-term->kind tterm) 'fncallp))
             (iff (good-typed-term-p tterm options)
                  (good-typed-fncall-p tterm options))))
  (defthm good-typed-term-list-of-nil
    (good-typed-term-list-p nil options))
  )

(local (in-theory (disable pseudo-termp
                           symbol-listp
                           acl2::pseudo-termp-opener
                           pseudo-term-listp-of-symbol-listp)))

(verify-guards good-typed-term-p)

;; mrg: I added uniform-path-help-when-good-typed-term-list-p and
;;   uniform-path-cond?-when-good-typed-term-list-p.  These are really
;;   more-returns theorems of good-typed-term-listp, but when I try to
;;   state them as such, the proofs take much longer and then fail.
;;   I'm guessing that ACL2 gets lost when pseudo-termp is enabled.
;;   Rather figuring out the various theory hints that would make it
;;   work, I'm just stating the theorems here.
;;     Note that uniform-path-help-when-good-typed-term-list-p conjures up
;;   path-cond as a free variable that just happens to be equal to
;;     (typed-term-list->path-cond tterm-lst).  I suspect this will make it
;;   hard to apply the rule automatically, but it still may be useful in
;;   subsequent arguments about good-typed-term-list-p and
;;   uniform-path-cond?.  Thus, I'm admitting it as a disabled theorem.
(defthmd uniform-path-help-when-good-typed-term-list-p
  (implies (and (typed-term-list-p tterm-lst)
                (good-typed-term-list-p tterm-lst options)
                (equal (typed-term-list->path-cond tterm-lst) path-cond))
           (uniform-path-help tterm-lst path-cond))
  :hints(("Goal"
          :in-theory (enable good-typed-term-list-p uniform-path-help typed-term-list->path-cond))))

(defthm uniform-path-cond?-when-good-typed-term-list-p
  (implies (and (typed-term-list-p tterm-lst)
                (good-typed-term-list-p tterm-lst options))
           (uniform-path-cond? tterm-lst))
  :hints(("Goal"
          :in-theory (enable uniform-path-cond?)
          :use((:instance uniform-path-help-when-good-typed-term-list-p
                          (path-cond (typed-term-list->path-cond tterm-lst)))))))

;; mrg:  I added the hypothesis
;;         (equal (typed-term->path-cond tterm)
;;                (typed-term-list->path-cond tterm-lst))
;;  which is required to ensure uniform-path-cond?
(defthm good-typed-term-list-of-cons
  (implies (and (type-options-p options)
                (typed-term-p tterm)
                (good-typed-term-p tterm options)
                (typed-term-list-p tterm-lst)
                (good-typed-term-list-p tterm-lst options)
                (equal (typed-term->path-cond tterm)
                       (typed-term-list->path-cond tterm-lst)))
           (good-typed-term-list-p (cons tterm tterm-lst) options))
  :hints (("Goal"
           :in-theory (enable good-typed-term-list-p)
           :expand (good-typed-term-list-p (cons tterm tterm-lst) options))))

(defthm good-typed-term-of-car
  (implies (and (type-options-p options)
                (typed-term-list-p tterm-lst)
                (good-typed-term-list-p tterm-lst options)
                (consp tterm-lst))
           (good-typed-term-p (car tterm-lst) options))
  :hints (("Goal"
           :in-theory (enable good-typed-term-list-p)
           :expand (good-typed-term-list-p tterm-lst options))))

(defthm good-typed-term-list-of-cdr
  (implies (and (type-options-p options)
                (typed-term-list-p tterm-lst)
                (good-typed-term-list-p tterm-lst options)
                (consp tterm-lst))
           (good-typed-term-list-p (cdr tterm-lst) options))
  :hints (("Goal"
           :in-theory (enable good-typed-term-list-p)
           :expand (good-typed-term-list-p tterm-lst options))))


(defthm good-typed-term-list-of-make-typed-term-list
  (implies (and (typed-term-list-p tterm-lst)
                (type-options-p options)
                (good-typed-term-list-p tterm-lst options))
           (good-typed-term-list-p
            (make-typed-term-list (typed-term-list->term-lst tterm-lst)
                                  (typed-term-list->path-cond tterm-lst)
                                  (typed-term-list->judgements tterm-lst))
            options)))

(defthm good-typed-term-of-make-typed-term
  (good-typed-term-p (make-typed-term) options)
  :hints (("Goal" :in-theory (enable good-typed-term-p
                                     good-typed-quote-p
                                     is-conjunct-list?
                                     judgement-of-term))))

(defthm good-typed-term-of-make-typed-term-list-with-path-cond
  (good-typed-term-list-p (make-typed-term-list nil path-cond ''t)
                          options)
  :hints (("Goal" :in-theory (enable good-typed-term-list-p
                                     make-typed-term-list))))

(local
 (defthm crock
   (implies (pseudo-termp judges)
            (and (pseudo-termp `(if ,judges 't 'nil))
                 (consp `(if ,judges 't 'nil))
                 (consp (cdddr `(if ,judges 't 'nil))))))
 )

(defthm good-typed-term-of-0-input-fn
  (implies (and (symbolp fn)
                (not (equal fn 'quote))
                (not (equal fn 'if))
                (pseudo-termp path-cond)
                (pseudo-termp judges)
                (type-options-p options))
           (good-typed-term-p
            (typed-term `(,fn) path-cond `(if ,judges 't 'nil))
            options))
  :hints (("Goal"
           :in-theory (enable pseudo-termp good-typed-term-list-p)
           :expand (good-typed-fncall-p
                    (typed-term `(,fn) path-cond `(if ,judges 't 'nil))
                    options))))

;; -------------------------------------------------------------------
;; Theorems for destructors
;; TODO: simplify the proof

(defthm implies-of-good-typed-if
  (implies (and (typed-term-p tterm) (type-options-p options)
                (good-typed-if-p tterm options))
           (and (consp (cdr (typed-term->term tterm)))
                (consp (cddr (typed-term->term tterm)))
                (consp (cdddr (typed-term->term tterm)))
                (consp (typed-term->judgements tterm))
                (consp (cdr (typed-term->judgements tterm)))
                (consp (cddr (typed-term->judgements tterm)))
                (consp (caddr (typed-term->judgements tterm)))
                (consp (cdddr (typed-term->judgements tterm)))
                (not (cddddr (typed-term->judgements tterm)))
                (consp (cdr (caddr (typed-term->judgements tterm))))
                (consp (cddr (caddr (typed-term->judgements tterm))))
                (consp (caddr (caddr (typed-term->judgements tterm))))
                (consp (cddr (caddr (caddr (typed-term->judgements tterm)))))
                (consp (cdr (caddr (caddr (typed-term->judgements tterm)))))
                (consp (cdddr (caddr (typed-term->judgements tterm))))
                (not (cddddr (caddr (typed-term->judgements tterm))))
                (consp (cdddr (caddr (caddr (typed-term->judgements tterm)))))
                (not (cddddr (caddr (caddr (typed-term->judgements tterm)))))
                (pseudo-termp (cadr (typed-term->judgements tterm)))
                (pseudo-termp (cadr (caddr (typed-term->judgements tterm))))
                (good-typed-term-p
                 (typed-term (cadr (typed-term->term tterm))
                             (typed-term->path-cond tterm)
                             (cadr (caddr (typed-term->judgements tterm))))
                 options)
                (good-typed-term-p
                 (typed-term (caddr (typed-term->term tterm))
                             (list* 'if
                                    (simple-transformer (cadr (typed-term->term tterm)))
                                    (typed-term->path-cond tterm)
                                    '('nil))
                             (caddr (caddr (caddr (typed-term->judgements
                                                   tterm)))))
                 options)
                (good-typed-term-p
                 (typed-term
                  (cadddr (typed-term->term tterm))
                  (list* 'if
                         (simple-transformer (list 'not
                                                   (cadr (typed-term->term tterm))))
                         (typed-term->path-cond tterm)
                         '('nil))
                  (cadddr (caddr (caddr (typed-term->judgements tterm)))))
                 options)
                (pseudo-termp (caddr (caddr (caddr (typed-term->judgements
                                                    tterm)))))
                (pseudo-termp (cadddr (caddr (caddr (typed-term->judgements
                                                     tterm)))))))
  :hints (("Goal"
           :expand (good-typed-if-p tterm options))))

(defthm implies-of-good-typed-fncall
  (implies (and (typed-term-p tterm) (type-options-p options)
                (good-typed-fncall-p tterm options))
           (and (consp (typed-term->judgements tterm))
                (consp (cdr (typed-term->judgements tterm)))
                (consp (cddr (typed-term->judgements tterm)))
                (consp (cdddr (typed-term->judgements tterm)))
                (pseudo-termp (cadr (typed-term->judgements tterm)))
                (pseudo-termp (caddr (typed-term->judgements tterm)))
                (not (cddddr (typed-term->judgements tterm)))
                (good-typed-term-list-p
                 (make-typed-term-list (cdr (typed-term->term tterm))
                                       (typed-term->path-cond tterm)
                                       (caddr (typed-term->judgements tterm)))
                 options)))
  :hints (("Goal"
           :expand (good-typed-fncall-p tterm options))))

(defthm implies-of-good-typed-lambda
  (implies (and (typed-term-p tterm) (type-options-p options)
                (good-typed-lambda-p tterm options))
           (and (consp (typed-term->judgements tterm))
                (consp (cdr (typed-term->judgements tterm)))
                (consp (caddr (typed-term->judgements tterm)))
                (consp (cddr (typed-term->judgements tterm)))
                (consp (cdddr (typed-term->judgements tterm)))
                (consp (cadr (caddr (typed-term->judgements tterm))))
                (consp (car (cadr (caddr (typed-term->judgements tterm)))))
                (consp (cdr (caddr (typed-term->judgements tterm))))
                (consp (cdr (car (cadr (caddr (typed-term->judgements tterm))))))
                (consp (cddr (caddr (typed-term->judgements tterm))))
                (consp (cdddr (caddr (typed-term->judgements tterm))))
                (consp (cddr (car (cadr (caddr (typed-term->judgements tterm))))))
                (not (cddddr (typed-term->judgements tterm)))
                (not (cddddr (caddr (typed-term->judgements tterm))))
                (not (cdddr (car (cadr (caddr (typed-term->judgements
                                               tterm))))))
                (pseudo-termp (cadr (typed-term->judgements tterm)))
                (good-typed-term-list-p
                 (make-typed-term-list (cdr (typed-term->term tterm))
                                       (typed-term->path-cond tterm)
                                       (caddr (caddr (typed-term->judgements
                                                      tterm))))
                 options)
                (good-typed-term-p
                 (typed-term (caddr (car (typed-term->term tterm)))
                             (list* 'if
                                    (shadow-path-cond (cadr (car (typed-term->term tterm)))
                                                      (typed-term->path-cond tterm))
                                    (term-substitution (caddr (caddr (typed-term->judgements tterm)))
                                                       (pairlis$ (cdr (typed-term->term tterm))
                                                                 (cadr (car (typed-term->term tterm))))
                                                       t)
                                    '('nil))
                             (caddr (car (cadr (caddr (typed-term->judgements tterm))))))
                 options)))
  :hints (("Goal"
           :expand (good-typed-lambda-p tterm options))))

;; ---------------------------------------------
;;       Destructors for typed-terms
(local (in-theory (disable (:executable-counterpart typed-term))))

;; ifp destructors
(define typed-term-if->cond ((tterm typed-term-p)
                             (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm options))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'ifp)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       (cond-term (cadr tt.term))
       (cond-path-cond tt.path-cond)
       ((mv err cond-judgements)
        (case-match tt.judgements
          ((& & (& judge-cond . &) &)
           (mv nil judge-cond))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-if->cond
            "Malformed if judgements ~q0" tt.judgements)))
    (make-typed-term :term cond-term
                     :path-cond cond-path-cond
                     :judgements cond-judgements))
  ///
  (more-returns
   (new-tt (implies
            (and (typed-term-p tterm)
                 (type-options-p options)
                 (equal (typed-term->kind tterm) 'ifp)
                 (good-typed-term-p tterm options))
            (< (acl2-count (typed-term->term new-tt))
               (acl2-count (typed-term->term tterm))))
           :name acl2-count-of-typed-term-if->cond)))

(define typed-term-if->then ((tterm typed-term-p)
                             (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm options))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'ifp)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((list* & cond then-term &) tt.term)
       (then-path-cond `(if ,(simple-transformer cond)
                            ,tt.path-cond 'nil))
       ((mv err then-judgements)
        (case-match tt.judgements
          ((& & (& & (& & judge-then . &) &) &)
           (mv nil judge-then))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-if->then
            "Malformed if judgements ~q0" tt.judgements)))
    (make-typed-term :term then-term
                     :path-cond then-path-cond
                     :judgements then-judgements))
  ///
  (more-returns
   (new-tt (implies
            (and (typed-term-p tterm)
                 (type-options-p options)
                 (equal (typed-term->kind tterm) 'ifp)
                 (good-typed-term-p tterm options))
            (< (acl2-count (typed-term->term new-tt))
               (acl2-count (typed-term->term tterm))))
           :name acl2-count-of-typed-term-if->then)))

(define typed-term-if->else ((tterm typed-term-p)
                             (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'ifp)
              (good-typed-term-p tterm options))
  :returns (new-tt (and (typed-term-p new-tt) (good-typed-term-p new-tt options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'ifp)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((list & cond & else-term) tt.term)
       (else-path-cond `(if ,(simple-transformer `(not ,cond))
                            ,tt.path-cond 'nil))
       ((mv err else-judgements)
        (case-match tt.judgements
          ((& & (& & (& & & judge-else) &) &)
           (mv nil judge-else))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-if->else
            "Malformed if judgements ~q0" tt.judgements)))
    (make-typed-term :term else-term
                     :path-cond else-path-cond
                     :judgements else-judgements))
  ///
  (more-returns
   (new-tt (implies
            (and (typed-term-p tterm)
                 (type-options-p options)
                 (equal (typed-term->kind tterm) 'ifp)
                 (good-typed-term-p tterm options))
            (< (acl2-count (typed-term->term new-tt))
               (acl2-count (typed-term->term tterm))))
           :name acl2-count-of-typed-term-if->else)))

(define typed-term->top ((tterm typed-term-p)
                         (options type-options-p))
  :guard (and (or (equal (typed-term->kind tterm) 'ifp)
                  (equal (typed-term->kind tterm) 'lambdap)
                  (equal (typed-term->kind tterm) 'fncallp))
              (good-typed-term-p tterm options))
  :returns (new-tt typed-term-p)
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (or (equal (typed-term->kind tterm) 'ifp)
                              (equal (typed-term->kind tterm) 'lambdap)
                              (equal (typed-term->kind tterm) 'fncallp))
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((mv err top-judge)
        (case-match tt.judgements
          ((& top-judge & &)
           (mv nil top-judge))
          (& (mv t nil))))
       ((if err)
        (prog2$ (er hard? 'typed-term=>typed-term->top
                    "Malformed judgements ~q0" tt.judgements)
                (make-typed-term))))
    (make-typed-term :term tt.term
                     :path-cond tt.path-cond
                     :judgements top-judge))
  ///
  (more-returns
   (new-tt (implies (and (equal (typed-term->kind tterm)
                                'lambdap)
                         (good-typed-term-p tterm options)
                         (typed-term-p tterm)
                         (type-options-p options))
                    (and (consp (typed-term->term new-tt))
                         (pseudo-lambdap (car (typed-term->term new-tt)))))
           :name implies-of-typed-term->top)))

;; fncallp destructors
(define typed-term-fncall->actuals ((tterm typed-term-p)
                                    (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'fncallp)
              (good-typed-term-p tterm options))
  :guard-hints (("Goal"
                 :expand (good-typed-fncall-p tterm options)))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'fncallp)
                          (good-typed-term-p tterm options))))
        nil)
       ((typed-term tt) tterm)
       ((cons & actuals) tt.term)
       ((mv err actuals-judgements)
        (case-match tt.judgements
          ((& & actuals-judge . &)
           (mv nil actuals-judge))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-fncall->actuals
            "Malformed fncall judgements ~q0" tt.judgements)))
    (make-typed-term-list actuals tt.path-cond actuals-judgements))
  ///
  (more-returns
   (new-ttl (implies (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'fncallp)
                          (good-typed-term-p tterm options))
                     (< (acl2-count
                         (typed-term-list->term-lst new-ttl))
                        (acl2-count (typed-term->term tterm))))
            :name acl2-count-of-make-typed-fncall)))

;; lambdap destructors
(define typed-term-lambda->actuals ((tterm typed-term-p)
                                    (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'lambdap)
              (good-typed-term-p tterm options))
  :guard-hints (("Goal"
                 :expand (good-typed-lambda-p tterm options)))
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'lambdap)
                          (good-typed-term-p tterm options))))
        nil)
       ((typed-term tt) tterm)
       ((cons & actuals) tt.term)
       ((mv err actuals-judgements)
        (case-match tt.judgements
          ((& & (& & actuals-judge . &) &)
           (mv nil actuals-judge))
          (& (mv t nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-lambda->actuals
            "Malformed lambda judgements ~q0" tt.judgements)))
    (make-typed-term-list actuals tt.path-cond actuals-judgements))
  ///
  (more-returns
   (new-ttl (implies (and (typed-term-p tterm)
                          (equal (typed-term->kind tterm)
                                 'lambdap)
                          (good-typed-term-p tterm options))
                     (< (acl2-count
                         (typed-term-list->term-lst new-ttl))
                        (acl2-count (typed-term->term tterm))))
            :name acl2-count-of-typed-term-lambda->actuals)
   ;; (new-ttl (implies (and (typed-term-p tterm)
   ;;                        (type-options-p options)
   ;;                        (equal (typed-term->kind tterm)
   ;;                               'lambdap)
   ;;                        (good-typed-term-p tterm options))
   ;;                   (equal (len (cdr (typed-term->term tterm)))
   ;;                          (len (typed-term-list->term-lst new-ttl))))
   ;;          :name typed-term-lambda->actuals-preserve-len
   ;;          :hints (("Goal"
   ;;                   :in-theory (enable typed-term-list->term-lst)
   ;;                   :expand (typed-term-lambda->actuals tterm options))))
   ))

(define typed-term-lambda->body ((tterm typed-term-p)
                                 (options type-options-p))
  :guard (and (equal (typed-term->kind tterm) 'lambdap)
              (good-typed-term-p tterm options))
  :guard-hints (("Goal"
                 :expand (good-typed-lambda-p tterm options)))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options)))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'lambdap)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((cons fn actuals) tt.term)
       (formals (lambda-formals fn))
       (body (lambda-body fn))
       (shadowed-path-cond (shadow-path-cond formals tt.path-cond))
       ((mv err body-judgements actuals-judges)
        (case-match tt.judgements
          ((& & (& ((& & body-judge) . &) actuals-judges &) &)
           (mv nil body-judge actuals-judges))
          (& (mv t nil nil))))
       ((if err)
        (er hard? 'typed-term=>typed-term-lambda->body
            "Malformed lambda judgements ~q0" tt.judgements))
       (substed-actuals-judgements
        (term-substitution actuals-judges (pairlis$ actuals formals) t)))
    (make-typed-term :term body
                     :path-cond `(if ,shadowed-path-cond
                                     ,substed-actuals-judgements 'nil)
                     :judgements body-judgements))
  ///
  (more-returns
   (new-tt (implies (and (typed-term-p tterm)
                         (type-options-p options)
                         (equal (typed-term->kind tterm)
                                'lambdap)
                         (good-typed-term-p tterm options))
                    (< (acl2-count (typed-term->term new-tt))
                       (acl2-count (typed-term->term tterm))))
           :name acl2-count-of-typed-term-lambda->body)))

;; --------------------------------------------------------------------
;;      Constructors

(defthm kind-of-make-typed-if
  (implies
   (and (typed-term-p tt-top)
        (typed-term-p tt-cond)
        (typed-term-p tt-then)
        (typed-term-p tt-else)
        (good-typed-term-p tt-cond options)
        (good-typed-term-p tt-then options)
        (good-typed-term-p tt-else options))
   (equal (typed-term->kind
           (typed-term (list 'if
                             (typed-term->term tt-cond)
                             (typed-term->term tt-then)
                             (typed-term->term tt-else))
                       (typed-term->path-cond tt-top)
                       (list* 'if
                              (typed-term->judgements tt-top)
                              (list* 'if
                                     (typed-term->judgements tt-cond)
                                     (list 'if
                                           (typed-term->term tt-cond)
                                           (typed-term->judgements tt-then)
                                           (typed-term->judgements tt-else))
                                     '('nil))
                              '('nil))))
          'ifp))
  :hints (("Goal"
           :in-theory (enable typed-term->kind))))

(define make-typed-if ((tt-top typed-term-p)
                       (tt-cond typed-term-p)
                       (tt-then typed-term-p)
                       (tt-else typed-term-p)
                       (options type-options-p))
  :guard (and (good-typed-term-p tt-cond options)
              (good-typed-term-p tt-then options)
              (good-typed-term-p tt-else options))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options))
                   :hints (("Goal"
                            :in-theory (enable good-typed-if-p))))
  (b* (((unless (mbt (and (type-options-p options)
                          (typed-term-p tt-top)
                          (typed-term-p tt-cond)
                          (typed-term-p tt-then)
                          (typed-term-p tt-else)
                          (good-typed-term-p tt-cond options)
                          (good-typed-term-p tt-then options)
                          (good-typed-term-p tt-else options))))
        (make-typed-term))
       ((typed-term ttp) tt-top)
       ((typed-term ttc) tt-cond)
       ((typed-term ttt) tt-then)
       ((typed-term tte) tt-else)
       ((unless (and (equal ttc.path-cond ttp.path-cond)
                     (equal ttt.path-cond
                            `(if ,(simple-transformer ttc.term)
                                 ,ttc.path-cond 'nil))
                     (equal tte.path-cond
                            `(if ,(simple-transformer `(not ,ttc.term))
                                 ,ttc.path-cond 'nil))))
        (prog2$
         (er hard? 'typed-term=>make-typed-term-if
             "Inconsistent inputs.~%")
         (make-typed-term))))
    (make-typed-term
     :term `(if ,ttc.term ,ttt.term ,tte.term)
     :path-cond ttp.path-cond
     :judgements
     `(if ,ttp.judgements
          (if ,ttc.judgements
              (if ,ttc.term ,ttt.judgements ,tte.judgements)
            'nil)
        'nil))))

(local
 (defthm pseudo-termp-of-lambda
   (implies (and (symbol-listp formals)
                 (pseudo-termp body-judge)
                 (pseudo-term-listp actuals)
                 (equal (len formals) (len actuals)))
            (pseudo-termp
             `((lambda ,formals ,body-judge) ,@actuals)))
   :hints (("Goal"
            :in-theory (enable pseudo-termp))))
 )

(defthm kind-of-make-typed-lambda
  (implies
   (and (typed-term-p tt-top)
        (typed-term-p tt-body)
        (typed-term-list-p tt-actuals)
        (good-typed-term-p tt-body options)
        (good-typed-term-list-p tt-actuals options)
        (pseudo-lambdap (car (typed-term->term tt-top))))
   (equal (typed-term->kind
           (typed-term
            (typed-term->term tt-top)
            (typed-term->path-cond tt-top)
            (list* 'if
                   (typed-term->judgements tt-top)
                   (list* 'if
                          (cons (list 'lambda
                                      (cadr (car (typed-term->term tt-top)))
                                      (typed-term->judgements tt-body))
                                (typed-term-list->term-lst tt-actuals))
                          (typed-term-list->judgements tt-actuals)
                          '('nil))
                   '('nil))))
          'lambdap))
  :hints (("Goal"
           :in-theory (enable typed-term->kind))))

(define make-typed-lambda ((tt-top typed-term-p)
                           (tt-body typed-term-p)
                           (tt-actuals typed-term-list-p)
                           (options type-options-p))
  :guard (and (good-typed-term-p tt-body options)
              (good-typed-term-list-p tt-actuals options))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options))
                   :hints (("Goal"
                            :in-theory (enable good-typed-lambda-p))))
  (b* (((unless (mbt (and (type-options-p options)
                          (typed-term-p tt-top)
                          (typed-term-p tt-body)
                          (typed-term-list-p tt-actuals)
                          (good-typed-term-p tt-body options)
                          (good-typed-term-list-p tt-actuals options))))
        (make-typed-term))
       ((typed-term ttt) tt-top)
       ((typed-term ttb) tt-body)
       (tta.term-lst (typed-term-list->term-lst tt-actuals))
       (tta.path-cond (typed-term-list->path-cond tt-actuals))
       (tta.judgements (typed-term-list->judgements tt-actuals))
       ((unless (and (consp ttt.term)
                     (pseudo-lambdap (car ttt.term))))
        (prog2$ (er hard? 'typed-term=>make-typed-term-lambda
                    "Inconsistent inputs.~%")
                (make-typed-term)))
       (formals (lambda-formals (car ttt.term)))
       (body (lambda-body (car ttt.term)))
       (actuals (cdr ttt.term))
       (body-path-cond
        `(if ,(shadow-path-cond formals ttt.path-cond)
             ,(term-substitution tta.judgements
                                 (pairlis$ tta.term-lst formals) t)
           'nil))
       (- (cw "formals: ~p0 actuals ~p1 body: ~p2~%" formals actuals body))
       (- (cw "tta.term-lst: ~q0" tta.term-lst))
       (- (cw "ttb.path-cond: ~q0" ttb.path-cond))
       (- (cw "ttb.term: ~q0" ttb.term))
       (- (cw "body-path-cond: ~q0" body-path-cond))
       (- (cw "ttt.path-cond: ~q0" ttt.path-cond))
       (- (cw "tta.path-cond: ~q0" tta.path-cond))
       ((unless (and (equal tta.term-lst actuals)
                     (equal body ttb.term)
                     (equal (len formals) (len actuals))
                     (equal ttb.path-cond body-path-cond)
                     (equal ttt.path-cond tta.path-cond)))
        (prog2$ (er hard? 'typed-term=>make-typed-term-lambda
                    "Inconsistent inputs.~%")
                (make-typed-term))))
    (make-typed-term
     :term ttt.term
     :path-cond ttt.path-cond
     :judgements `(if ,ttt.judgements
                      (if ((lambda ,formals
                             ,ttb.judgements)
                           ,@actuals)
                          ,tta.judgements
                        'nil)
                    'nil))))

(defthm kind-of-make-typed-fncall
  (implies
   (and (typed-term-p tt-top)
        (typed-term-list-p tt-actuals)
        (good-typed-term-list-p tt-actuals options)
        (consp (typed-term->term tt-top))
        (symbolp (car (typed-term->term tt-top)))
        (not (equal (car (typed-term->term tt-top)) 'quote))
        (not (equal (car (typed-term->term tt-top)) 'if))
        (equal (cdr (typed-term->term tt-top))
               (typed-term-list->term-lst tt-actuals))
        (equal (typed-term->path-cond tt-top)
               (typed-term-list->path-cond tt-actuals)))
   (equal (typed-term->kind
           (typed-term (typed-term->term tt-top)
                       (typed-term->path-cond tt-top)
                       (list* 'if
                              (typed-term->judgements tt-top)
                              (typed-term-list->judgements tt-actuals)
                              '('nil))))
          'fncallp))
  :hints (("Goal"
           :in-theory (enable typed-term->kind))))

(define make-typed-fncall ((tt-top typed-term-p)
                           (tt-actuals typed-term-list-p)
                           (options type-options-p))
  :guard (good-typed-term-list-p tt-actuals options)
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options))
                   :hints (("Goal"
                            :in-theory (enable good-typed-fncall-p))))
  (b* (((unless (mbt (and (typed-term-p tt-top)
                          (typed-term-list-p tt-actuals)
                          (type-options-p options)
                          (good-typed-term-list-p tt-actuals options))))
        (make-typed-term))
       ((typed-term ttt) tt-top)
       (tta.term-lst (typed-term-list->term-lst tt-actuals))
       (tta.path-cond (typed-term-list->path-cond tt-actuals))
       (tta.judgements (typed-term-list->judgements tt-actuals))
       ((unless (and (consp ttt.term)
                     (symbolp (car ttt.term))
                     (equal (cdr ttt.term) tta.term-lst)
                     (equal ttt.path-cond tta.path-cond)
                     (not (equal (car ttt.term) 'quote))
                     (not (equal (car ttt.term) 'if))))
        (prog2$ (er hard? 'typed-term=>make-typed-fncall
                    "Inconsistent inputs.~%")
                (make-typed-term))))
    (make-typed-term
     :term ttt.term
     :path-cond ttt.path-cond
     :judgements `(if ,ttt.judgements ,tta.judgements 'nil))))
