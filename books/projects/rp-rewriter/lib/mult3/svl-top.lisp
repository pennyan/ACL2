; MULTIPLIER RULES

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

(include-book "fnc-defs")

(include-book "svl-spec")

(include-book "meta-top")

(include-book "mult-rules")

(include-book "adder-rules")

(include-book "centaur/svl/top" :dir :system)

(include-book "doc")

(local
 (include-book "lemmas"))

(attach-meta-fncs svl-mult-rules)

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(encapsulate
  nil

  (local
   (use-arithmetic-5 t))

  (defthm bits-is-bit-of-nosyntaxp
    (implies (and (integerp num)
                  (natp start))
             (equal (svl::bits num start 1)
                    (bit-of num start)))
    :hints (("Goal"
             :in-theory (e/d (bitp
                              oddp
                              evenp
                              bit-of
                              SV::4VEC-PART-SELECT
                              svl::bits
                              SV::4VEC->LOWER
                              SV::2VEC
                              SV::4VEC-RSH
                              SV::4VEC->UPPER
                              SV::4VEC-ZERO-EXT

                              SV::4VEC
;SV::4VEC-CONCAT
                              SV::4VEC-SHIFT-CORE
;LOGHEAD
                              logbitp
                              ifix
                              mod
                              expt
                              ash
                              logbit
                              loghead
                              )
                             (SVL::BITP-BITS-SIZE=1
                              ;;loghead
                              (:REWRITE SV::4VEC-EQUAL)

                              (:DEFINITION ACL2::EXPT2$INLINE)
;(:DEFINITION ACL2::IMOD$INLINE)

                              (:REWRITE ACL2::REMOVE-WEAK-INEQUALITIES)
                              SVL::CONVERT-4VEC-CONCAT-TO-4VEC-CONCAT$
                              SVL::4VEC-ZERO-EXT-IS-BITS
                              SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
                              SVL::4VEC-CONCAT$-OF-SIZE=1-TERM2=0

                              SVL::4VEC-PART-SELECT-IS-BITS)))))

  (def-rp-rule bits-is-bit-of
    (implies (and (integerp num)
                  (natp start)
                  (syntaxp (atom (ex-from-rp num))))
             (equal (svl::bits num start 1)
                    (bit-of num start)))
    :hints (("Goal"
             :in-theory (e/d (bits-is-bit-of-nosyntaxp) ()))))

  (def-rp-rule integerp-of-nth
    (implies (and (integer-listp lst)
                  (natp index)
                  (< index (len lst)))
             (integerp (nth index lst)))
    :hints (("Goal"
             :in-theory (e/d (sum)
                             (+-IS-SUM)))))

  (def-rp-rule bits-is-bit-of-for-nth
    (implies (and (natp start)
                  (force (natp x))
                  (force (< x (len y)))
                  (integer-listp y))
             (equal (svl::bits (nth x y) start 1)
                    (bit-of (nth x y) start)))
    :hints (("Goal"
             :in-theory (e/d (bits-is-bit-of-nosyntaxp) ()))))

  (defthmd bits-is-bit-of-reverse
    (implies (and (integerp num)
                  (natp start))
             (equal (bit-of num start)
                    (svl::bits num start 1)))))

(def-rp-rule bits-of-bit-of
  (equal (svl::bits (bit-of x pos) 0 1)
         (bit-of x pos))
  :otf-flg t
  :hints (("Goal"
           :do-not '(preprocess)
           :cases ((bitp (bit-of x pos)))
           :in-theory (e/d (bitp)
                           (BITP-OF-BIT-OF
                            (:TYPE-PRESCRIPTION BIT-OF))))
          ("Subgoal 2"
           :in-theory (e/d () ()))))

(progn
  (def-rp-rule 4vec-bitxor-is-binary-xor-when-bitp
    (implies (and (bitp x)
                  (bitp y))
             (and (equal (sv::4vec-bitxor x y)
                         (binary-xor x y))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-bitxor-is-binary-xor-when-integerp-1
    (implies (and (integerp x)
                  (natp start)
                  (bitp y))
             (and (equal (sv::4vec-bitxor (svl::bits x start 1)  y)
                         (binary-xor (bit-of x start) y))
                  (equal (sv::4vec-bitxor y (svl::bits x start 1))
                         (binary-xor y (bit-of x start)))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-bitxor-is-binary-xor-when-integerp-2
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (integerp y))
             (and (equal (sv::4vec-bitxor (svl::bits x start1 1) (svl::bits y start2 1))
                         (binary-xor (bit-of x start1) (bit-of y start2)))))
    :hints (("goal"
             :in-theory (e/d (bitp) ())))))




(progn
  (encapsulate
    nil
    (local
     (use-arithmetic-5 t))
    (def-rp-rule
      4vec-bitand-to-binary-and-when-atleast-one-is-bitp
      (implies (or (and (bitp x)
                        (force (integerp y)))
                   (and (bitp y)
                        (force (integerp x))))
               (equal (sv::4vec-bitand x y)
                      (binary-and (svl::bits x 0 1)
                                  (svl::bits y 0 1))))
      :hints (("Goal"
               :in-theory (e/d (bitp
                                bit-of
                                svl::Bits
                                SV::4VEC-PART-SELECT
                                SV::3VEC-BITAND
                                SV::4VEC->UPPER
                                SV::4VEC->LOWER
                                SV::3VEC-FIX
                                sv::4vec-bitand
                                )
                               (mod2-is-m2
                                +-IS-SUM
                                floor2-if-f2))))))
  
  (def-rp-rule 4vec-bitand-is-binary-and-when-bitp
    (implies (and (bitp x)
                  (bitp y))
             (and (equal (sv::4vec-bitand x y)
                         (binary-and x y))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-bitand-is-binary-and-when-integerp-1
    (implies (and (integerp x)
                  (natp start)
                  (bitp y))
             (and (equal (sv::4vec-bitand (svl::bits x start 1)  y)
                         (binary-and (bit-of x start) y))
                  (equal (sv::4vec-bitand y (svl::bits x start 1))
                         (binary-and y (bit-of x start)))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-bitand-is-binary-and-when-integerp-2
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (integerp y))
             (and (equal (sv::4vec-bitand (svl::bits x start1 1) (svl::bits y start2 1))
                         (binary-and (bit-of x start1) (bit-of y start2)))))
    :hints (("goal"
             :in-theory (e/d (bitp) ())))))

(progn
  (def-rp-rule 4vec-bitor-is-binary-or-when-bitp
    (implies (and (bitp x)
                  (bitp y))
             (and (equal (sv::4vec-bitor x y)
                         (binary-or x y))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-bitor-is-binary-or-when-integerp-1
    (implies (and (integerp x)
                  (natp start)
                  (bitp y))
             (and (equal (sv::4vec-bitor (svl::bits x start 1)  y)
                         (binary-or (bit-of x start) y))
                  (equal (sv::4vec-bitor y (svl::bits x start 1))
                         (binary-or y (bit-of x start)))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-bitor-is-binary-or-when-integerp-2
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (integerp y))
             (and (equal (sv::4vec-bitor (svl::bits x start1 1) (svl::bits y start2 1))
                         (binary-or (bit-of x start1) (bit-of y start2)))))
    :hints (("goal"
             :in-theory (e/d (bitp) ())))))

(progn
  (def-rp-rule 4vec-?-is-binary-?-when-bitp
    (implies (and (bitp x)
                  (bitp y)
                  (bitp z))
             (equal (sv::4vec-? x y z)
                    (binary-? x y z)))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-?-is-binary-?-when-integerp-1
    (implies (and (integerp x)
                  (natp start)
                  (bitp y)
                  (bitp z))
             (and (equal (sv::4vec-? (svl::bits x start 1) y z)
                         (binary-? (bit-of x start) y z))
                  (equal (sv::4vec-? y (svl::bits x start 1) z)
                         (binary-? y (bit-of x start) z))
                  (equal (sv::4vec-? y z (svl::bits x start 1))
                         (binary-? y z (bit-of x start)))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-?-is-binary-?-when-integerp-2
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (integerp y)
                  (bitp z))
             (and (equal (sv::4vec-? (svl::bits x start1 1) (svl::bits y start2 1) z)
                         (binary-? (bit-of x start1) (bit-of y start2) z))
                  (equal (sv::4vec-? (svl::bits x start1 1) z (svl::bits y start2 1))
                         (binary-? (bit-of x start1) z (bit-of y start2)))
                  (equal (sv::4vec-? z (svl::bits x start1 1) (svl::bits y start2 1))
                         (binary-? z (bit-of x start1) (bit-of y start2)))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-?-is-binary-?-when-integerp-3
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (natp start3)
                  (integerp y)
                  (integerp z))
             (and (equal (sv::4vec-? (svl::bits x start1 1) (svl::bits y start2 1) (svl::bits z start3 1))
                         (binary-? (bit-of x start1) (bit-of y start2) (bit-of z start3)))
                  ))
    :hints (("goal"
             :in-theory (e/d (bitp) ())))))

(progn
  (def-rp-rule 4vec-?*-is-binary-?-when-bitp
    (implies (and (bitp x)
                  (bitp y)
                  (bitp z))
             (equal (sv::4vec-?* x y z)
                    (binary-? x y z)))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-?*-is-binary-?-when-integerp-1
    (implies (and (integerp x)
                  (natp start)
                  (bitp y)
                  (bitp z))
             (and (equal (sv::4vec-?* (svl::bits x start 1) y z)
                         (binary-? (bit-of x start) y z))
                  (equal (sv::4vec-?* y (svl::bits x start 1) z)
                         (binary-? y (bit-of x start) z))
                  (equal (sv::4vec-?* y z (svl::bits x start 1))
                         (binary-? y z (bit-of x start)))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-?*-is-binary-?-when-integerp-2
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (integerp y)
                  (bitp z))
             (and (equal (sv::4vec-?* (svl::bits x start1 1) (svl::bits y start2 1) z)
                         (binary-? (bit-of x start1) (bit-of y start2) z))
                  (equal (sv::4vec-?* (svl::bits x start1 1) z (svl::bits y start2 1))
                         (binary-? (bit-of x start1) z (bit-of y start2)))
                  (equal (sv::4vec-?* z (svl::bits x start1 1) (svl::bits y start2 1))
                         (binary-? z (bit-of x start1) (bit-of y start2)))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-?*-is-binary-?-when-integerp-3
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (natp start3)
                  (integerp y)
                  (integerp z))
             (and (equal (sv::4vec-?* (svl::bits x start1 1) (svl::bits y start2 1) (svl::bits z start3 1))
                         (binary-? (bit-of x start1) (bit-of y start2) (bit-of z start3)))
                  ))
    :hints (("goal"
             :in-theory (e/d (bitp) ())))))

(encapsulate
  nil

  (local
   (use-arithmetic-5 t))

  (def-rp-rule convert-4vec-bitnot$-binary-not-0
    (implies (and (integerp x))
             (equal (svl::4vec-bitnot$ 1 x)
                    (binary-not (bit-of x 0))))
    :hints (("Goal"
             :in-theory (e/d (bitp
                              SV::4VEC-BITNOT
                              SV::3VEC-BITNOT
                              SV::4VEC->LOWER
                              SV::4VEC->UPPER
                              SV::4VEC
                              SV::4VEC-PART-SELECT
                              svl::4vec-bitnot$
                              bit-of
                              not$
                              m2
                              f2
                              SV::4VEC-CONCAT
                              )
                             (+-IS-SUM
                              MOD2-IS-M2
                              floor2-if-f2
                              SVL::4VEC-CONCAT$-OF-SIZE=1-TERM2=0
                              SVL::EQUAL-OF-4VEC-CONCAT-WITH-SIZE=1)))))

  (def-rp-rule convert-4vec-bitnot$-binary-not-1
    (implies (bitp x)
             (equal (svl::4vec-bitnot$ 1 x)
                    (binary-not x)))
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule convert-4vec-bitnot$-binary-not-2
    (implies (and (integerp x)
                  (natp start))
             (equal (svl::4vec-bitnot$ 1 (svl::bits x start 1))
                    (binary-not (bit-of x start))))
    :hints (("Goal"
             :in-theory (e/d (bitp) ())))))

(def-rp-rule 4vec-fix=-of-binary-fns
  (and (equal (svl::4vec-fix (binary-not s))
              (binary-not s))
       (equal (svl::4vec-fix (or$ x y))
              (or$ x y))
       (equal (svl::4vec-fix (and$ x y))
              (and$ x y))
       (equal (svl::4vec-fix (binary-xor x y))
              (binary-xor x y))
       (equal (svl::4vec-fix (adder-and x y))
              (adder-and x y))
       (equal (svl::4vec-fix (m2 x))
              (m2 x))
       (equal (svl::4vec-fix (f2 x))
              (f2 x))))

(encapsulate
  nil

  (local
   (use-arithmetic-5 t))

  (defthmd bits-of-binary-fns-lemma
    (implies (and (not (zp start))
                  (bitp x))
             (equal (svl::bits x start 1 )
                    0)))

  (defthmd bits-of-binary-fns-lemma-2
    (implies (and (posp size)
                  (bitp x))
             (equal (svl::bits x 0 size )
                    x)))

  (def-rp-rule bits-of-binary-fns
    (implies (not (zp start))
             (and (equal (svl::bits (or$ x y) start 1 )
                         0)
                  (equal (svl::bits (and$ x y) start 1 )
                         0)
                  (equal (svl::bits (and-list hash-code x) start 1 )
                         0)
                  (equal (svl::bits (not$ x) start 1 )
                         0)
                  (equal (svl::bits (binary-xor x y) start 1 )
                         0)
                  (equal (svl::bits (binary-? x y z) start 1 )
                         0)
                  (equal (svl::bits (bit-of x y) start 1 )
                         0)
                  (equal (svl::bits (ADDER-AND x y) start 1 )
                         0)))
    :hints (("goal"
             :do-not '(preprocess)
             :in-theory (e/d (bits-of-binary-fns-lemma)
                             (svl::4vec-part-select-is-bits
                              +-IS-SUM
                              SVL::4VEC-ZERO-EXT-IS-BITS
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-concat$-of-size=1-term2=0
                              svl::4vec-zero-ext-is-4vec-concat)))))

  (def-rp-rule bits-of-binary-fns-start=0
    (implies (posp size)
             (and (equal (svl::bits (or$ x y) 0 size )
                         (or$ x y))
                  (equal (svl::bits (and$ x y) 0 size )
                         (and$ x y))
                  (equal (svl::bits (and-list hash-code x) 0 size )
                         (and-list hash-code x))
                  (equal (svl::bits (not$ x) 0 size )
                         (not$ x))
                  (equal (svl::bits (binary-xor x y) 0 size )
                         (binary-xor x y))
                  (equal (svl::bits (binary-? x y z) 0 size )
                         (binary-? x y z))
                  (equal (svl::bits (bit-of x y) 0 size )
                         (bit-of x y))
                  (equal (svl::bits (ADDER-AND x y) 0 size )
                         (ADDER-AND x y))))
    :hints (("goal"
             :do-not '(preprocess)
             :in-theory (e/d (bits-of-binary-fns-lemma-2)
                             (svl::4vec-part-select-is-bits
                              BITS-IS-BIT-OF
                              +-IS-SUM
                              SVL::4VEC-ZERO-EXT-IS-BITS
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-concat$-of-size=1-term2=0
                              svl::4vec-zero-ext-is-4vec-concat))))))

(encapsulate
  nil

  (local
   (use-arithmetic-5 t))

  (local
   (defthm lemma1
     (implies (and (not (zp start))
                   (bitp x))
              (equal (bit-of x start)
                     0))
     :hints (("Goal"
              :in-theory (e/d (bitp bit-of) ())))))

  (local
   (defthm lemma2
     (implies (and (bitp x))
              (equal (bit-of x 0)
                     x))
     :hints (("Goal"
              :in-theory (e/d (bitp bit-of) ())))))

  (def-rp-rule$ t t
    bit-of-binary-fns
    (implies (not (zp start))
             (and (equal (bit-of (or$ x y) start )
                         0)
                  (equal (bit-of (and$ x y) start)
                         0)
                  (equal (bit-of (not$ x) start)
                         0)
                  (equal (bit-of (binary-xor x y) start )
                         0)
                  (equal (bit-of (binary-? x y z) start )
                         0)))
    :hints (("goal"
             :do-not '(preprocess)
             :in-theory (e/d (bitp)
                             (svl::4vec-part-select-is-bits
                              EQUAL-SIDES-TO-S
                              SVL::4VEC-ZERO-EXT-IS-BITS
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-concat$-of-size=1-term2=0
                              svl::4vec-zero-ext-is-4vec-concat)))))

  (def-rp-rule$ t t
    bit-of-binary-fns-start=0
    (implies t
             (and (equal (bit-of (or$ x y) 0 )
                         (or$ x y))
                  (equal (bit-of (and$ x y) 0)
                         (and$ x y))
                  (equal (bit-of (not$ x) 0)
                         (not$ x))
                  (equal (bit-of (binary-xor x y) 0)
                         (binary-xor x y))
                  (equal (bit-of (binary-? x y z) 0)
                         (binary-? x y z))))
    :hints (("goal"
             :do-not '(preprocess)
             :in-theory (e/d ()
                             (svl::4vec-part-select-is-bits
                              SVL::4VEC-ZERO-EXT-IS-BITS
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-concat$-of-size=1-term2=0
                              svl::4vec-zero-ext-is-4vec-concat))))))

(def-rp-rule bits-of-4vec-==-binary-fncs
  (and (equal (SVL::BITS (SV::4VEC-== (BINARY-OR x y) 1) '0 '1)
              (BINARY-OR x y))
       (equal (SVL::BITS (SV::4VEC-== (BINARY-and x y) 1) '0 '1)
              (BINARY-and x y)))
  :hints (("Goal"
           :in-theory (e/d (bitp and$ or$)
                           (EQUAL-SIDES-TO-S)))))

(def-rp-rule$ t t
  bit-of-4vec-bitnot-main
  (implies (bitp x)
           (equal (BIT-OF (SV::4VEC-BITNOT x) 0)
                  (svl::4vec-bitnot$ 1 x)))
  :hints (("Goal"
           :in-theory (e/d (bitp) (bitp-of-bit-of
                                   (:TYPE-PRESCRIPTION BIT-OF)
                                   )))))

(def-rp-rule$ t t
  bit-of-4vec-bitnot
  (equal (BIT-OF (SV::4VEC-BITNOT (bit-of x start)) 0)
         (svl::4vec-bitnot$ 1 (bit-of x start)))
  :hints (("Goal"
           :use ((:instance bitp-of-bit-of
                            (num x)
                            (pos start)))
           :in-theory (e/d (bitp) (bitp-of-bit-of
                                   (:TYPE-PRESCRIPTION BIT-OF))))))

(def-rp-rule 4vec-fix-of-bit-of
  (equal (svl::4vec-fix (bit-of x pos))
         (bit-of x pos))
  :hints (("Goal"
           :in-theory (e/d (bit-of
                            bitp)
                           (bit-fix)))))

(def-rp-rule
  integerp-of-bit-of
  (b* ((res (bit-of num pos))) (integerp res))
  :rule-classes :rewrite)

;; (def-rp-rule 4vec-concat$-of-and$-commutes
;;   (implies (syntaxp (pp-and$-order x y))
;;            (equal (svl::4vec-concat$ size
;;                                 (and$ y x)
;;                                 rest)
;;                   (svl::4vec-concat$ size
;;                                 (and$ x y)
;;                                 rest)))
;;   :hints (("Goal"
;;            :in-theory (e/d (and$) ()))))

(def-rp-rule 3vec-fix-of-binary-fncs
  (and (equal (SV::3VEC-FIX (binary-and a b))
              (binary-and a b))
       (equal (SV::3VEC-FIX (binary-or a b))
              (binary-or a b))
       (equal (SV::3VEC-FIX (binary-xor a b))
              (binary-xor a b))
       (equal (SV::3VEC-FIX (binary-? a b c))
              (binary-? a b c))
       (equal (SV::3VEC-FIX (binary-not a))
              (binary-not a)))
  :hints (("Goal"
           :in-theory (e/d (binary-?
                            binary-and
                            binary-not
                            binary-or
                            binary-xor)
                           (equal-sides-to-s)))))

(def-rp-rule 3vec-fix-of-bit-of
  (implies t
           (equal (sv::3vec-fix (bit-of x index))
                  (bit-of x index))))

#|(def-rp-rule bits-of-adder-and
  (equal (svl::bits (adder-and a b) 0 1)
         (adder-and a b))
  :hints (("Goal"
           :in-theory (e/d (adder-and) ()))))||#

(local
 (defthm bits-when-bitp-start=0
   (implies (bitp x)
            (equal (svl::bits x 0 1)
                   x))
   :hints (("Goal"
            :in-theory (e/d (bitp) ())))))

(def-rp-rule bits-0-1-of-s
  (equal (svl::bits (s hash-code pp c/d) 0 1)
         (s hash-code pp c/d))
  :hints (("Goal"
           :in-theory (e/d () ()))))

(def-rp-rule bits-0-1-of-m2
  (equal (svl::bits (m2 x) 0 1)
         (m2 x))
  :hints (("Goal"
           :in-theory (e/d () ()))))

(def-rp-rule bits-1-1-of-s
  (implies (and (not (zp start))
                (natp size))
           (equal (svl::bits (s hash-code pp c/d) start size)
                  0)))

(def-rp-rule bits-1-1-of-m2
  (implies (and (not (zp start))
                (natp size))
           (equal (svl::bits (m2 x) start size)
                  0)))

(def-rp-rule equal-of-concat$-with-hyp
  (implies (equal x1 x2)
           (equal (equal (svl::4vec-concat$ 1 x1 rest1)
                         (svl::4vec-concat$ 1 x2 rest2))
                  (equal (sv::4vec-fix rest1)
                         (sv::4vec-fix rest2))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(rp::def-rp-rule
 bits-of-c-when-bit-when-start>0
 (implies (and (bitp (rp::c hash-code x y z))
               (posp start))
          (equal (svl::bits (rp::c hash-code x y z) start 1)
                 0))
 :hints (("Goal"
          :in-theory (e/d (bitp) ()))))

(rp::def-rp-rule
 bits-of-c-when-bit-when-start-0
 (implies (and (bitp (rp::c hash-code x y z)))
          (equal (svl::bits (rp::c hash-code x y z) 0 1)
                 (rp::c  hash-code x y z)))
 :hints (("Goal"
          :in-theory (e/d (bitp) ()))))

(defthm bits-of-c-when-bit-when-start-0-side-cond
  (implies (and (bitp (rp::c hash-code x y z)))
           (bitp (rp::c hash-code x y z)))
  :rule-classes nil)

(rp-attach-sc bits-of-c-when-bit-when-start-0
              bits-of-c-when-bit-when-start-0-side-cond)

(rp::def-rp-rule
 bits-of-s-c-res-when-bit-when-start>0
 (implies (and (bitp (rp::s-c-res x y z))
               (posp start))
          (equal (svl::bits (rp::s-c-res x y z) start 1)
                 0))
 :hints (("Goal"
          :in-theory (e/d (bitp) ()))))

(rp::def-rp-rule
 bits-of-s-c-res-when-bit-when-start=0
 (implies (and (bitp (rp::s-c-res x y z)))
          (equal (svl::bits (rp::s-c-res x y z) 0 1)
                 (rp::s-c-res x y z)))
 :hints (("Goal"
          :in-theory (e/d (bitp) ()))))

(defthm
  bits-of-s-c-res-when-bit-when-start=0-side-cond
  (implies (and (bitp (rp::s-c-res x y z)))
           (bitp (rp::s-c-res x y z)))
  :rule-classes nil)

(rp-attach-sc bits-of-s-c-res-when-bit-when-start=0
              bits-of-s-c-res-when-bit-when-start=0-side-cond)

(def-rp-rule
  concat-of-adder-and-is-f2
  (implies (bitp other)
           (and (equal (svl::4vec-concat$ size
                                          (adder-and (bit-of x y) other)
                                          other2)
                       (svl::4vec-concat$ size
                                          (f2 (adder-sum (bit-of x y) other))
                                          other2))
                (equal (svl::4vec-concat$ size
                                          other2
                                          (adder-and (bit-of x y) other))
                       (svl::4vec-concat$ size
                                          other2
                                          (f2 (adder-sum (bit-of x y) other))))))
  :hints (("Goal"
           :cases ((bitp (bit-of x y)))
           :in-theory (e/d (bitp)
                           ((:TYPE-PRESCRIPTION BIT-OF)
                            (:REWRITE BITP-OF-BIT-OF))))))

(def-rp-rule$ t t
  4vec-concat$-1-of-binary-and
  (equal (svl::4vec-concat$ 1 (and$ x y) z)
         (svl::4vec-concat$ 1 (s-spec (list (and$ x y))) z))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

(encapsulate
  nil
  (local
   (use-arithmetic-5 t))
  (defthmd insert-redundant-loghead-to-bits
    (implies (and (integerp a)
                  (natp x)
                  (natp y))
             (equal (svl::bits a x y)
                    (svl::bits (loghead (+ x y) a) x y)))
    :hints (("Goal"
             :in-theory (e/d (svl::bits
                              sum
                              SV::4VEC->UPPER
                              SV::4VEC-SHIFT-CORE
                              SV::4VEC->LOWER
                              SV::4VEC-RSH
                              SV::4VEC-CONCAT
                              SV::4VEC-PART-SELECT)
                             (+-IS-SUM)))))
  (def-rp-rule bits-of-*
    (implies (and (integerp a)
                  (integerp b)
                  (natp x)
                  (natp y))
             (equal (svl::bits (* a b) x y)
                    (svl::bits (loghead (+ x y) (* a b)) x y)))
    :hints (("Goal"
             :use ((:instance insert-redundant-loghead-to-bits
                              (a (* a b))))
             :in-theory (e/d () ())))))



(def-rp-rule nth-of-cons
  (and (equal (nth 0 (cons a b)) a)
       (implies (posp index)
                (equal (nth index (cons a b))
                       (nth (1- index) b)))))

(def-rp-rule integer-listp-of-cons
  (equal (integer-listp (cons a b))
         (and (integerp a)
              (integer-listp b))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For when definitions of ha and fa modules are replaced with + sign:

;; it is necessary to create this rewrite mechanism because when output of an
;; ha becomes and input of another ha, it messes up with the system somehow and
;; some full-adders are not simplified as they are supposed to. So I looked at
;; the rw stack for svl::bits-of-4vec-plus-is-4vec-plus-start=0 and
;; svl::bits-of-4vec-plus-is-4vec-plus to figure out what fa and ha are
;; rewritten to. And I decided to rewrite summation of single bit SV::4VEC-PLUS
;; to temp-ha-spec. If it is added with another SV::4VEC-PLUS, then it is
;; probably a part of a full-adder, so I convert that to fa spec.
;; For other adder types, other rewrite rules might be necessary.

(defun temp-ha-spec (x y)
  (svl::4vec-list (ss x y)
                  (cc x y)))


(encapsulate
  nil
  (local
   (use-arithmetic-5 t))

  (def-rp-rule
    4vec-plus-of-bits-to-temp-ha-spec-1
    (implies (and (bitp x)
                  (bitp y)
                  (integerp size)
                  (> size 0))
             (equal (svl::bits (sv::4vec-plus x y)
                               1 size)
                    (svl::bits (temp-ha-spec x y) 1 1)))
    :hints (("goal"
             :in-theory (e/d (bitp
                              sum
                              svl::bits
                              sv::4vec-part-select
                              sv::4vec->upper
                              sv::4vec->lower
                              sv::4vec-concat)
                             (+-is-sum)))))
  

  (def-rp-rule
    4vec-plus-of-bits-to-temp-ha-spec-2
    (implies (and (bitp x)
                  (bitp y))
             (equal (svl::bits (sv::4vec-plus x y)
                               0 1)
                    (svl::bits (temp-ha-spec x y) 0 1)))
    :hints (("goal"
             :in-theory (e/d (bitp
                              sum
                              svl::bits
                              sv::4vec-part-select
                              sv::4vec->upper
                              sv::4vec->lower
                              sv::4vec-concat)
                             (+-is-sum)))))
  
  (def-rp-rule
    4vec-plus-of-bits-to-temp-ha-spec-3
    (implies (and (bitp x)
                  (bitp y)
                  (integerp size)
                  (> size 1))
             (equal (svl::bits (sv::4vec-plus x y)
                               0 size)
                    (temp-ha-spec x y)))
    :hints (("goal"
             :in-theory (e/d (bitp
                              sum
                              svl::bits
                              sv::4vec-part-select
                              sv::4vec->upper
                              sv::4vec->lower
                              sv::4vec-concat)
                             (+-is-sum)))))

  
  (def-rp-rule
    4vec-plus-rule-for-fa
    (implies (and (bitp x)
                  (bitp y)
                  (bitp z)
                  (integerp size)
                  (> size 1))
             (equal (svl::bits (sv::4vec-plus (temp-ha-spec x y)
                                              z)
                               0 size)
                    (svl::4vec-list (ss x y z)
                                    (cc x y z))))
    :hints (("goal"
             :in-theory (e/d (bitp
                              sum
                              svl::bits
                              sv::4vec-part-select
                              sv::4vec->upper
                              sv::4vec->lower
                              sv::4vec-concat)
                             (+-is-sum)))))

  (def-rp-rule
    4vec-plus-rule-for-fa-to-ss
    (implies (and (bitp x)
                  (bitp y)
                  (bitp z))
             (equal (svl::bits (sv::4vec-plus (temp-ha-spec x y)
                                              z)
                               0 1)
                    (ss x y z)))
    :hints (("goal"
             :in-theory (e/d (bitp
                              sum
                              svl::bits
                              sv::4vec-part-select
                              sv::4vec->upper
                              sv::4vec->lower
                              sv::4vec-concat)
                             (+-is-sum)))))

  (def-rp-rule
    4vec-plus-rule-for-fa-to-cc
    (implies (and (bitp x)
                  (bitp y)
                  (bitp z))
             (equal (svl::bits (sv::4vec-plus (temp-ha-spec x y)
                                              z)
                               1 1)
                    (cc x y z)))
    :hints (("goal"
             :in-theory (e/d (bitp
                              sum
                              svl::bits
                              sv::4vec-part-select
                              sv::4vec->upper
                              sv::4vec->lower
                              sv::4vec-concat)
                             (+-is-sum)))))

  (def-rp-rule 4vec-concat$-of-temp-ha-spec
    (implies (and (bitp x)
                  (bitp y)
                  (integerp size)
                  (> size 1))
             (equal (svl::4vec-concat$ size
                                       (temp-ha-spec x y)
                                       0)
                    (temp-ha-spec x y)))
    :hints (("goal"
             :in-theory (e/d (bitp
                              SV::4VEC-CONCAT
                              SV::4VEC->LOWER
                              SV::4VEC->UPPER
                              svl::4vec-concat$)
                             ()))))

  (def-rp-rule bits-of-temp-ha-spec-out-of-range
    (implies (and (bitp x)
                  (bitp y)
                  (posp size)
                  (integerp start)
                  (> start 1)) 
             (equal (svl::bits (temp-ha-spec x y)
                               start size)
                    0))
    :hints (("Goal"
             :in-theory (e/d (svl::bits
                              f2 sum
                              bitp
                              SV::4VEC-RSH
                              SV::4VEC-CONCAT
                              SV::4VEC-SHIFT-CORE
                              SV::4VEC->UPPER
                              SV::4VEC->LOWER
                              SV::4VEC-PART-SELECT)
                             (+-is-sum
                              floor2-if-f2
                              mod2-is-m2)))))

  )

(def-rp-rule
  bits-0-1-of-temp-ha-spec
  (equal (svl::bits (temp-ha-spec x y) 0 1)
         (ss x y))
  :hints (("Goal"
           ;;:cases ((M2 (SUM-LIST (LIST X Y))))
           :in-theory (e/d (S-SPEC-TO-ADDER-M2) ()))))

(def-rp-rule
  bits-1-1-of-temp-ha-spec
  (implies (and (bitp x)
                (bitp y))
           (equal (svl::bits (temp-ha-spec x y) 1 1)
                  (cc x y)))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(def-rp-rule integerp-temp-ha-spec
  (implies (and (integerp x)
                (integerp y))
           (integerp (temp-ha-spec x y))))




;;;;;;;;;;;;;;;;;;;;

(def-rp-rule svex-env-fix$inline-opener
  (implies (sv::svex-env-p x)
           (equal (sv::svex-env-fix$inline x)
                  x)))

(def-rp-rule sv::svex-alist-eval-for-symbolic-is-svex-alist-eval
  (equal (sv::svex-alist-eval-for-symbolic x y z)
         (sv::svex-alist-eval x y)))

(bump-all-meta-rules)
