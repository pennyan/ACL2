; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>


(in-package "RP")
(include-book "../rp-rewriter")
(include-book "aux-function-lemmas")
(include-book "local-lemmas")
(include-book "proof-functions")
(include-book "rp-equal-lemmas")
(include-book "proof-function-lemmas")

(make-flag rp-apply-bindings :defthm-macro-name defthm-apply-bindings)

(in-theory (disable rp-iff-flag rp-lhs rp-rhs rp-hyp))

(encapsulate
  nil
  ;; rp-apply-bindings returns pseuod-termp2

  (local
   (defthm lemma1
     (implies (and (pseudo-term-listp (strip-cdrs bindings))
                   (alistp bindings))
              (pseudo-termp (cdr (assoc-equal term bindings))))))

  (local
   (defthm lemma2
     (implies (and (pseudo-term-listp lst)
                   (not (equal s 'quote))
                   (symbolp s))
              (pseudo-termp (cons s lst)))))

  (local
   (defthm lemma3
     (implies (and (pseudo-termp term)
                   (not (equal (car term) 'quote))
                   (consp term)
                   (atom (car term)))
              (symbolp (car term)))))


  (defthm len-of-rp-apply-bindings-subterms-is-len-of-subterms
    (equal (len (rp-apply-bindings-subterms subterms bindings))
           (len subterms)))

  (defthm-apply-bindings
    (defthm rp-apply-bindings-is-pseudo-termp2
      (implies (and (pseudo-termp2 term)
                    (bindings-alistp bindings))
               (pseudo-termp2 (rp-apply-bindings term bindings)))
      :flag rp-apply-bindings)

    (defthm rp-apply-bindings-subterms-is-pseudo-termp2
      (implies (and (pseudo-term-listp2 subterms)
                    (bindings-alistp bindings))
               (pseudo-term-listp2 (rp-apply-bindings-subterms subterms bindings)))
      :flag rp-apply-bindings-subterms)))

(encapsulate
  nil

  ;; rule for
  ;; (equal (rp-evl (rp-apply-bindings term bindings) a)
  ;;        (rp-evl term (bind-bindings bindings a)))

  (defun bind-bindings-aux (b1 b2)
    (declare (ignorable b1 b2))
    (if (atom b1)
        nil
      (cons (cons (caar b1) (rp-evl (cdar b1) b2))
            (bind-bindings-aux (cdr b1) b2))))

  (defmacro bind-bindings (b1 b2)
    `(append (bind-bindings-aux ,b1 ,b2) ,b2))

  (local
   (defthm lemma1
     (implies (and (not (consp (assoc-equal term bindings)))
                   (alistp bindings))
              (not (consp (assoc-equal term (bind-bindings-aux bindings a)))))))

  (local
   (defthm lemma2
     (implies (and
               (not (consp term))
               (symbolp term)
               term (alistp a)
               (alistp bindings)
               (symbol-listp (strip-cars bindings))
               (pseudo-term-listp2 (strip-cdrs bindings))
               (consp (assoc-equal term bindings)))
              (equal (rp-evl (cdr (assoc-equal term bindings))
                             a)
                     (cdr (assoc-equal term
                                       (append (bind-bindings-aux bindings a)
                                               a)))))))

  (local
   (defthm lemma3
     (implies (and
               (not (consp term))
               (symbolp term)
               term (alistp a)
               (alistp bindings)
               (symbol-listp (strip-cars bindings))
               (pseudo-term-listp2 (strip-cdrs bindings))
               (not (consp (assoc-equal term bindings))))
              (equal (equal (cdr (assoc-equal term a))
                            (cdr (assoc-equal term
                                              (append (bind-bindings-aux bindings a)
                                                      a))))
                     t))))

  (local
   (defthm lemma4
     (implies
      (and (consp term)
           (not (equal (car term) 'quote))
           (case-split (symbolp (car TERM)))
           (equal (rp-evl-lst (rp-apply-bindings-subterms (cdr term)
                                                          bindings)
                              a)
                  (rp-evl-lst (cdr term)
                              (append (bind-bindings-aux bindings a)
                                      a)))
           (true-listp (cdr term))
           (pseudo-term-listp2 (cdr term))

           (alistp a)
           (alistp bindings)
           (symbol-listp (strip-cars bindings))
           (pseudo-term-listp2 (strip-cdrs bindings)))
      (equal (equal (rp-evl (cons (car term)
                                  (rp-apply-bindings-subterms (cdr term)
                                                              bindings))
                            a)
                    (rp-evl term
                            (append (bind-bindings-aux bindings a)
                                    a)))
             t))
     :hints (("goal" :in-theory (enable rp-evl-of-fncall-args)))))

  (local
   (defthm lemma5
     (implies
      (and
       (consp term)
       (not (equal (car term) 'quote))
       (case-split (symbolp (car term)))
       (not (consp (cdr term)))
       (alistp a)
       (alistp bindings)
       (symbol-listp (strip-cars bindings))
       (pseudo-term-listp2 (strip-cdrs bindings)))
      (equal (rp-evl (list (car term)) a)
             (rp-evl term
                     (append (bind-bindings-aux bindings a)
                             a))))
     :hints (("goal" :in-theory (enable rp-evl-of-fncall-args)))))

  (local
   (defthm lemma6
     (IMPLIES (AND (CONSP TERM)
                   (NOT (EQUAL 'QUOTE (CAR TERM)))
                   (SYMBOLP (CAR TERM))
                   (NOT (CDR TERM))
                   (ALISTP A)
                   (ALISTP BINDINGS)
                   (SYMBOL-LISTP (STRIP-CARS BINDINGS))
                   (PSEUDO-TERM-LISTP2 (STRIP-CDRS BINDINGS)))
              (EQUAL (RP-EVL (RP-APPLY-BINDINGS TERM BINDINGS)
                             A)
                     (RP-EVL TERM
                             (APPEND (BIND-BINDINGS-AUX BINDINGS A)
                                     A))))))

  (local
   (defthm lemma7
     (implies (consp subterms)
              (EQUAL (RP-EVL-LST (RP-APPLY-BINDINGS-SUBTERMS SUBTERMS BINDINGS)
                                 A)
                     (CONS (RP-EVL (RP-APPLY-BINDINGS (CAR SUBTERMS)
                                                      BINDINGS)
                                   A)
                           (RP-EVL-LST (RP-APPLY-BINDINGS-SUBTERMS (CDR SUBTERMS)
                                                                   BINDINGS)
                                       A))))))

  (defthm-apply-bindings
    (defthm rp-apply-bindings-to-evl
      (implies (and (pseudo-termp2 term)
                    (alistp a)
                    (bindings-alistp bindings))
               (equal (rp-evl (rp-apply-bindings term bindings) a)
                      (rp-evl term (bind-bindings bindings a))))
      :flag rp-apply-bindings)

    (defthm rp-apply-bindings-subterms-to-evl-lst
      (implies (and (pseudo-term-listp2 subterms)
                    (alistp a)
                    (bindings-alistp bindings))
               (equal (rp-evl-lst (rp-apply-bindings-subterms subterms bindings) a)
                      (rp-evl-lst subterms (bind-bindings bindings a))))
      :flag rp-apply-bindings-subterms)
    :hints (("Goal"
             :expand ((RP-APPLY-BINDINGS TERM BINDINGS)
                      (RP-APPLY-BINDINGS-SUBTERMS NIL BINDINGS))
             :in-theory (e/d () (lambda-exp-free-listp
                                 rp-apply-bindings
                                 rp-apply-bindings-subterms
                                 lambda-exp-free-p))))
    :otf-flg t))

(defthm rp-apply-bindings-equiv-iff
  (implies (and (valid-rulep rule)
                (alistp a)
                (rp-evl (rp-apply-bindings (rp-hyp rule) bindings) a)
                (bindings-alistp bindings)
                (rp-iff-flag rule))
           (iff (rp-evl (rp-apply-bindings (rp-lhs rule) bindings) a)
                (rp-evl (rp-apply-bindings (rp-rhs rule) bindings) a)))
  :hints (("goal" :in-theory (disable valid-rulep-sk-necc)
           :use (:instance valid-rulep-sk-necc
                           (a (bind-bindings bindings a))))))

(defthm rp-apply-bindings-equiv-not-iff
  (implies (and (valid-rulep rule)
                (alistp a)
                (rp-evl (rp-apply-bindings (rp-hyp rule) bindings) a)
                (bindings-alistp bindings)
                (not (rp-iff-flag rule)))
           (equal (rp-evl (rp-apply-bindings (rp-lhs rule) bindings) a)
                  (rp-evl (rp-apply-bindings (rp-rhs rule) bindings) a)))
  :hints (("goal" :in-theory (disable valid-rulep-sk-necc)
           :use (:instance valid-rulep-sk-necc
                           (a (bind-bindings bindings a))))))


(encapsulate
  nil

  (defthmd  rp-equal2-bindings-1to1-remove-bindings-from-rp
    (implies (and (bindings-alistp bindings))
             (rp-equal2-bindings-1to1 (remove-rp-from-bindings bindings)
                                      bindings))
    :hints (("goal"
             :induct (remove-rp-from-bindings bindings)
             :do-not-induct t
             :expand (rp-equal2-bindings-1to1
                      (cons (cons (car (car bindings))
                                  (ex-from-rp (cdr (car bindings))))
                            (remove-rp-from-bindings (cdr bindings)))
                      bindings)
             :in-theory (enable ex-from-rp-loose
                                remove-rp-from-bindings))))

  (defthmd rp-equal2-bindings-1to1-consp
    (implies (rp-equal2-bindings-1to1 bindings bindings2)
             (equal (consp bindings2) (consp bindings)))
    :hints (("goal"
             :expand (rp-equal2-bindings-1to1 bindings bindings2))))

  (defthmd rp-equal2-bindings-1to1-consp-2
    (implies (and (bindings-alistp bindings)
                  (bindings-alistp bindings2)
                  (rp-equal2-bindings-1to1 bindings bindings2))
             (equal (consp (assoc-equal term bindings2))
                    (consp (assoc-equal term bindings))))
    :hints (("goal"
             :in-theory (enable rp-equal2-bindings-1to1)
             :induct (rp-equal2-bindings-1to1 bindings bindings2) )))

  (defthmd rp-equal2-bindings-1to1-assoc-eq
    (implies (and (bindings-alistp bindings)
                  (bindings-alistp bindings2)
                  (consp (assoc-equal term bindings))
                  (rp-equal2-bindings-1to1 bindings bindings2))
             (rp-equal2 (cdr (assoc-equal term bindings))
                        (cdr (assoc-equal term bindings2))))
    :hints (("goal"
             :in-theory (enable rp-equal2-bindings-1to1)
             :induct (rp-equal2-bindings-1to1 bindings bindings2)))))

(defthm-apply-bindings
  (defthm valid-falist-apply-bindings
    (implies (and (all-falist-consistent-bindings bindings)
                  (not (include-fnc term 'falist)))
             (all-falist-consistent (rp-apply-bindings term bindings)))
    :flag rp-apply-bindings)
  (defthm valid-falist-apply-bindings-subterms
    (implies (and (all-falist-consistent-bindings bindings)
                  (not (include-fnc-subterms subterms 'falist)))
             (all-falist-consistent-lst
              (rp-apply-bindings-subterms subterms bindings)))
    :flag rp-apply-bindings-subterms))

(encapsulate
  nil

  (local
   (defthm lemma1
     (implies
      (and (symbolp term)
           term
           (bindings-alistp bindings)
           (consp (assoc-equal term
                               (remove-rp-from-bindings bindings))))
      (equal (rp-evl (cdr (assoc-equal term
                                       (remove-rp-from-bindings bindings)))
                     a)
             (rp-evl (cdr (assoc-equal term bindings))
                     a)))))

  (local
   (defthm lemma2
     (implies (and (bindings-alistp bindings)
                   (consp (assoc-equal term (remove-rp-from-bindings bindings))))
              (consp (assoc-equal term bindings)))))

  (local
   (defthm lemma3
     (implies (and (bindings-alistp bindings)
                   (not (consp (assoc-equal term (remove-rp-from-bindings bindings)))))
              (not (consp (assoc-equal term bindings))))))

  (defthm-apply-bindings
    (defthm rp-apply-bindings-with-remove-rp-from-bindings
      (implies
       (and (pseudo-termp2 term)
            (bindings-alistp bindings))
       (equal (rp-evl (rp-apply-bindings term (remove-rp-from-bindings bindings)) a)
              (rp-evl (rp-apply-bindings term bindings) a)))
      :flag rp-apply-bindings)

    (defthm rp-apply-bindings-subterms-remove-rp-from-bindings
      (implies
       (and (pseudo-term-listp2 subterms)
            (bindings-alistp bindings))
       (equal (rp-evl-lst (rp-apply-bindings-subterms subterms (remove-rp-from-bindings bindings)) a)
              (rp-evl-lst (rp-apply-bindings-subterms subterms bindings) a)))
      :flag rp-apply-bindings-subterms)

    :hints (("goal" :in-theory (enable rp-evl-of-fncall-args))))

  (local
   (defthm lemma4
     (implies (and (all-falist-consistent
                    (cdr (assoc-equal term bindings)))
                   (consp (assoc-equal term bindings)))
              (all-falist-consistent
               (cdr (assoc-equal term (remove-rp-from-bindings bindings)))))))

  (defthm-apply-bindings
    (defthm valid-falist-apply-bindings-with-remove-rp-from-bindings
      (implies (and (all-falist-consistent-bindings bindings)
                    (bindings-alistp bindings)
                    (not (include-fnc term 'falist)))
               (all-falist-consistent
                (rp-apply-bindings term
                                   (remove-rp-from-bindings bindings))))
      :flag rp-apply-bindings)
    (defthm valid-falist-apply-bindings-subterms-with-remove-rp-from-bindings
      (implies (and (all-falist-consistent-bindings bindings)
                    (bindings-alistp bindings)
                    (not (include-fnc-subterms subterms 'falist)))
               (all-falist-consistent-lst
                (rp-apply-bindings-subterms subterms (remove-rp-from-bindings bindings))))
      :flag rp-apply-bindings-subterms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  nil

  (local
   (defthm lemma1
     (implies (and (RP-SYNTAXP TERM)
                   (NOT (EQUAL (CAR TERM) 'QUOTE)))
              (RP-SYNTAXP-LST (CDR TERM)))
     :hints (("Goal"
              :cases ((is-rp term))
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma2
     (implies (is-rp term)
              (is-rp (rp-apply-bindings term bindings)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma3
     (implies (is-rp term)
              (equal (rp-apply-bindings (cadr term) bindings)
                     (cadr term)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma4
     (IMPLIES (AND
               (CONSP TERM)
               (NOT (CONSP (CDDR TERM)))
               (CONSP (CDR TERM))
               (RP-SYNTAXP (CADR TERM))
               (EQUAL (CAR TERM) 'RP)
               (IS-RP TERM))
              (IS-RP (LIST 'RP (CADR TERM))))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma5
     (IMPLIES (AND
               (CONSP TERM)
               (NOT (EQUAL (CAR TERM) 'QUOTE))
               (NOT (EQUAL (CAR TERM) 'SYNP))
;(NOT (CONSP (CAR TERM)))
               (RP-SYNTAXP-LST (RP-APPLY-BINDINGS-SUBTERMS (CDR TERM)
                                                           BINDINGS))
               (RP-SYNTAXP TERM)
               (RP-SYNTAXP-LST (STRIP-CDRS BINDINGS)))
              (RP-SYNTAXP (CONS (CAR TERM)
                                (RP-APPLY-BINDINGS-SUBTERMS (CDR TERM)
                                                            BINDINGS))))
     :hints (("Goal"
              :cases ((is-rp term))
              :in-theory (e/d (is-rp) ())))))

  (defthm-apply-bindings
    (defthm rp-syntaxp-rp-apply-bindings
      (implies (and (rp-syntaxp term)
                    (pseudo-termp2 term)
                    (rp-syntaxp-bindings bindings))
               (rp-syntaxp (rp-apply-bindings term bindings)))
      :flag rp-apply-bindings)
    (defthm rp-syntaxp-rp-apply-bindings-subterms
      (implies (and (rp-syntaxp-lst subterms)
                    (pseudo-term-listp2 subterms)
                    (rp-syntaxp-bindings bindings))
               (rp-syntaxp-lst
                (rp-apply-bindings-subterms subterms bindings)))
      :flag rp-apply-bindings-subterms)
    :hints (("Goal"
             :in-theory (e/d (is-rp) ())))))

(encapsulate
  nil

  (local
   (defthm lemma1
     (IMPLIES (AND (NOT (CONSP TERM))
                   (VALID-SC-BINDINGS BINDINGS A)
                   (CONSP (ASSOC-EQUAL TERM BINDINGS)))
              (VALID-SC (CDR (ASSOC-EQUAL TERM BINDINGS))
                        A))))

  (local
   (defthm lemma2
     (implies (NOT (EQUAL car-term 'RP))
              (not (is-rp (cons car-term
                                x))))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma3
     (implies (is-if term)
              (CASE-MATCH TERM (('IF & & &) T)
                (& NIL)))
     :hints (("Goal"
              :in-theory (e/d (is-if) ())))))

  (local
   (in-theory (disable is-synp)))

  (local
   (defthm lemma4
     (equal (cdr (RP-APPLY-BINDINGS-SUBTERMS SUBTERMS BINDINGS))
            (RP-APPLY-BINDINGS-SUBTERMS (cdr SUBTERMS) BINDINGS))))

  (local
   (defthm lemma5
     (implies (consp subterms)
              (equal (car (RP-APPLY-BINDINGS-SUBTERMS SUBTERMS BINDINGS))
                     (RP-APPLY-BINDINGS (CAR SUBTERMS)  BINDINGS)))))

  (local
   (defthm lemma6
     (implies (and (is-if term)
                   (rp-syntaxp term))
              (and (rp-syntaxp (cadr term))
                   (rp-syntaxp (caddr term))
                   (rp-syntaxp (cadddr term))))
     :hints (("Goal"
              :in-theory (e/d (is-if) ())))
     :rule-classes :forward-chaining))

  (local
   (defthm lemma7
     (implies (is-if term)
              (CASE-MATCH TERM (('IF & & &) T)
                (& NIL)))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (is-if) ())))))

  (local
   (defthm lemma8
     (implies (is-if term)
              (IS-IF (LIST* 'if
                            (RP-APPLY-BINDINGS (CADR TERM) BINDINGS)
                            (RP-APPLY-BINDINGS-SUBTERMS (CDDR TERM)
                                                        BINDINGS))))
     :hints (("Goal"
              :in-theory (e/d (is-if) ())))))

  (local
   (defthmd lemma9-lemma1
     (implies (not (is-if term))
              (not (is-if (CONS (CAR TERM)
                                (RP-APPLY-BINDINGS-SUBTERMS (CDR TERM)
                                                            BINDINGS)))))
     :hints (("Goal"
              :expand (RP-APPLY-BINDINGS-SUBTERMS (CDDDDR TERM)
                                                  BINDINGS)
              :in-theory (e/d (is-if) ())))))

  (local
   (defthmd lemma9-lemma2
     (implies (and (not (is-rp term))
                   (rp-syntaxp term))
              (not (is-rp (CONS (CAR TERM)
                                (RP-APPLY-BINDINGS-SUBTERMS (CDR TERM)
                                                            BINDINGS)))))
     :hints (("Goal"
              :expand (RP-APPLY-BINDINGS-SUBTERMS (CDDDDR TERM)
                                                  BINDINGS)
              :in-theory (e/d (is-if) ())))))

  (local
   (defthmd IS-LAMBDA-STRICT-of-apply-bindings
     (implies (is-lambda term)
              (equal (RP-APPLY-BINDINGS TERM BINDINGS)
                     (cons (car term)
                           (rp-apply-bindings-subterms (cdr term)
                                                       BINDINGS))))
     :hints (("Goal"
              :in-theory (e/d (is-synp) ())))))

  (defthm valid-sc-cons
    (implies (and (not (is-rp term))
                  (rp-syntaxp term)
;(not (consp (car term)))
                  (valid-sc-subterms (cdr term) a))
             (valid-sc term a))
    :hints (("goal"
             :expand ((valid-sc (cons car-term subterms) a)
                      (valid-sc term a)
                      (valid-sc-subterms (cdr term) a))
             :cases ((is-if term))
             :in-theory (e/d (valid-sc) ()))))

  (local
   (defthm lemma9
     (implies (and (not (is-rp term))
                   (rp-syntaxp term)
                   (pseudo-termp2 term)
                   (rp-syntaxp-bindings bindings)
                   (bindings-alistp bindings)
;(not (consp (car term)))
                   (valid-sc-subterms (rp-apply-bindings-subterms (cdr term) bindings) a))
              (valid-sc (cons (car term)
                              (rp-apply-bindings-subterms (cdr term)
                                                          bindings))
                        a))
     :hints (("goal"
              :do-not-induct t
              ;; :use (:instance valid-sc-cons)

              :in-theory (e/d (valid-sc
                               rp-apply-bindings-subterms
                               valid-sc-cons
                               )
                              (ex-from-rp
                               not-include-rp-means-rp-syntaxp
                               not-include-rp-means-rp-syntaxp-lst))))))

  (defthm-apply-bindings
    (defthmd valid-sc-apply-bindings-for-hyp-lemma
      (implies
       (and (not (include-fnc term 'rp))
            (bindings-alistp bindings)
            (pseudo-termp2 term)
            (rp-syntaxp-bindings bindings)
            (valid-sc-bindings bindings a))
       (valid-sc (rp-apply-bindings term bindings) a))
      :flag rp-apply-bindings)
    (defthmd valid-sc-apply-bindings-subterms-for-hyp-lemma
      (implies
       (and (not (include-fnc-subterms subterms 'rp))
            (bindings-alistp bindings)
            (pseudo-term-listp2 subterms)
            (rp-syntaxp-bindings bindings)
            (valid-sc-bindings bindings a))
       (valid-sc-subterms (rp-apply-bindings-subterms subterms bindings) a))
      :flag rp-apply-bindings-subterms)
    :hints (("Goal"
             :in-theory (e/d () ()))))

  (defthm valid-sc-apply-bindings-for-hyp
    (implies (and (valid-rulep rule)
                  (bindings-alistp bindings)
                  (rp-syntaxp-bindings bindings)
                  (valid-sc-bindings bindings a))
             (valid-sc (rp-apply-bindings (rp-hyp rule) bindings) a))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (valid-sc-apply-bindings-for-hyp-lemma)
                             (rp-apply-bindings)))))

  (local
   (defthm lemma201
     (implies (valid-sc (RP-APPLY-BINDINGS (EX-FROM-RP TERM)
                                           BINDINGS)
                        a)
              (valid-sc (ex-from-rp (RP-APPLY-BINDINGS term BINDINGS)) a))
     :hints (("Goal"
              :induct (EX-FROM-RP TERM)
              :in-theory (e/d (ex-from-rp
                               is-rp) ())))))

  (local
   (defun eval-and-all-lst (lst a)
     (if (atom lst)
         t
       (and (eval-and-all (car lst) a)
            (eval-and-all-lst (cdr lst) a)))))

  (local
   (defun context-from-rp-bindings (bindings)
     (if (atom bindings)
         nil
       (cons (context-from-rp (cdar bindings) nil)
             (context-from-rp-bindings (cdr bindings))))))
  (local
   (encapsulate
     nil

     (local
      (defthm ilemma1
        (implies (atom bindings)
                 (and (equal (BIND-BINDINGS-AUX BINDINGS A)
                             nil)))))

     (local
      (defthm ilemma2
        (implies (and (rp-syntaxp term)
                      (case-split (consp term))
                      (not (is-rp term)))
                 (equal (CONTEXT-FROM-RP (RP-APPLY-BINDINGS TERM BINDINGS)
                                         NIL)
                        nil))
        :hints (("Goal"
                 :in-theory (e/d (is-rp context-from-rp rp-apply-bindings) ())))))

     (local
      (defthm ilemma3
        (implies (and (atom term)
                      (eval-and-all-lst (context-from-rp-bindings bindings) a))
                 (eval-and-all (CONTEXT-FROM-RP (RP-APPLY-BINDINGS TERM BINDINGS)
                                                NIL)
                               a))
        :hints (("Goal"
                 :in-theory (e/d (context-from-rp rp-apply-bindings) ())))))

     (local
      (defthm ilemma4
        (implies
         (and (is-rp term)
              (eval-and-all (context-from-rp (rp-apply-bindings (caddr term)
                                                                bindings)
                                             nil)
                            a)
              (rp-syntaxp term)
              (pseudo-termp2 term)
              (alistp a)
              (bindings-alistp bindings)
              (rp-syntaxp-bindings bindings)
              (rp-evl (list (cadr (cadr term))
                            (ex-from-rp (caddr term)))
                      (append (bind-bindings-aux bindings a)
                              a))
              (eval-and-all (context-from-rp (caddr term) nil)
                            (append (bind-bindings-aux bindings a)
                                    a))
              (eval-and-all-lst (context-from-rp-bindings bindings)
                                a))
         (eval-and-all (context-from-rp (rp-apply-bindings term bindings)
                                        nil)
                       a))
        :hints (("Goal"
                 :do-not-induct t
                 :expand ((rp-apply-bindings term bindings)
                          (CONTEXT-FROM-RP (LIST 'RP
                                                 (CADR TERM)
                                                 (RP-APPLY-BINDINGS (CADDR TERM)
                                                                    BINDINGS))
                                           NIL))
                 :in-theory (e/d (is-rp
                                  rp-evl-of-fncall-args)
                                 (context-from-rp
                                  EX-FROM-RP-LEMMA1))))))

     (defthm lemma202
       (implies (and (rp-syntaxp term)
                     (pseudo-termp2 term)
                     (alistp a)
                     (bindings-alistp bindings)
                     (rp-syntaxp-bindings bindings)
                     (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL)
                                   (APPEND (BIND-BINDINGS-AUX BINDINGS A) A))
                     (eval-and-all-lst (context-from-rp-bindings bindings) a))
                (EVAL-AND-ALL (CONTEXT-FROM-RP (rp-apply-bindings TERM bindings) NIL) a))
       :hints (("Goal"
                :induct (CONTEXT-FROM-RP TERM NIL)
                :in-theory (e/d (eval-and-all context-from-rp )
                                (BIND-BINDINGS-AUX is-rp
                                                   rp-apply-bindings)))))))

  (local
   (defthm lemma203
     (implies (and (EVAL-AND-ALL (CONTEXT-FROM-RP term NIL) A)
                   (VALID-SC (EX-FROM-RP term) A))
              (VALID-SC term A))
     :hints (("Goal"
              :induct (EX-FROM-RP term)
              :in-theory (e/d (ex-from-rp is-rp context-from-rp)
                              (EX-FROM-RP-LEMMA1))))))

  (local
   (defthm lemma204
     (implies (VALID-SC-BINDINGS BINDINGS A)
              (eval-and-all-lst (context-from-rp-bindings bindings) a))
     :hints (("Goal"
              :in-theory (e/d (context-from-rp is-rp) (EX-FROM-RP-LEMMA1))))))

  (defthm-valid-sc
    (defthm rp-apply-bindings-to-valid-sc-with-different-a
      (implies (and (pseudo-termp2 term)
                    (rp-syntaxp term)
                    (alistp a)
                    (valid-sc-bindings bindings a)
                    (rp-syntaxp-bindings bindings)
                    (valid-sc term (bind-bindings bindings a))
                    (bindings-alistp bindings))
               (valid-sc (rp-apply-bindings term bindings) a))
      :flag valid-sc)

    (defthm rp-apply-bindings-to-valid-sc-with-different-a-subterms
      (implies (and (pseudo-term-listp2 subterms)
                    (rp-syntaxp-lst subterms)
                    (alistp a)
                    (rp-syntaxp-bindings bindings)
                    (valid-sc-subterms subterms (bind-bindings bindings a))
                    (valid-sc-bindings bindings a)
                    (bindings-alistp bindings))
               (valid-sc-subterms (rp-apply-bindings-subterms subterms bindings) a))
      :flag valid-sc-subterms)
    :hints (("Goal"
             :induct
             (FLAG-VALID-SC FLAG TERM SUBTERMS (BIND-BINDINGS BINDINGS A))
             :in-theory (e/d (IS-LAMBDA-STRICT-of-apply-bindings)
                             (EVL-OF-EXTRACT-FROM-RP
                              VALID-SC-EX-FROM-RP-2)))))

  (defthm valid-sc-apply-bindings-for-rhs
    (implies
     (and (valid-rulep rule)
          (alistp a)
          (rp-syntaxp-bindings bindings)
          (valid-sc-bindings bindings a)
          (bindings-alistp bindings)
          (rp-evl (rp-apply-bindings (rp-hyp rule) bindings) a))
     (valid-sc (rp-apply-bindings (rp-rhs rule) bindings) a))
    :otf-flg t
    :hints (("Goal"
             :use ((:instance rp-apply-bindings-to-evl
                              (term (rp-hyp rule)))
                   (:instance rp-apply-bindings-to-valid-sc-with-different-a
                              (term (rp-rhs rule)))
                   (:instance valid-rulep-sk-necc
                              (a (bind-bindings bindings a)))
                   (:instance valid-sc-any-necc
                              (term (rp-rhs rule))
                              (a (bind-bindings bindings a))))
             :do-not-induct t
             :in-theory (e/d (valid-rulep
                              rule-syntaxp)
                             (rp-apply-bindings

                              valid-rulep-sk
                              valid-sc-any-necc
                              valid-rulep-sk-necc
                              valid-sc
                              valid-sc-any))))))
