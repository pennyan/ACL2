; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "a4vec")
(include-book "tools/templates" :dir :system)
(include-book "xdoc/alter" :dir :system)
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/gl/arith-lemmas" :dir :system))

(defmacro sv::aig-sterm (x)   `(gl::bfr-sterm ,x))
(defmacro sv::aig-scons (x y) `(gl::bfr-scons ,x ,y))
(defmacro sv::aig-ucons (x y) `(gl::bfr-ucons ,x ,y))


;; Some additional function that will be useful for avoiding intermediate
;; lists...

(defsymbolic bfr-logand-sss ((a s)
                             (b s)
                             (c s))
  :returns (and s (logand a (logand b c)))
  :measure (+ (len a) (len b) (len c))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b))
       ((mv cf cr cend) (first/rest/end c))
       (lsb (bfr-and af bf cf))
       ((when (and aend bend cend))
        (bfr-sterm lsb))
       (rest (bfr-logand-sss ar br cr)))
    (bfr-scons lsb rest)))

(defsymbolic bfr-logand-ssss ((a s)
                              (b s)
                              (c s)
                              (d s))
  :returns (and s (logand a (logand b (logand c d))))
  :measure (+ (len a) (len b) (len c) (len d))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b))
       ((mv cf cr cend) (first/rest/end c))
       ((mv df dr dend) (first/rest/end d))
       (lsb (bfr-and af bf cf df))
       ((when (and aend bend cend dend))
        (bfr-sterm lsb))
       (rest (bfr-logand-ssss ar br cr dr)))
    (bfr-scons lsb rest)))

(defsymbolic bfr-logior-sss ((a s)
                             (b s)
                             (c s))
  :returns (or s (logior a (logior b c)))
  :measure (+ (len a) (len b) (len c))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b))
       ((mv cf cr cend) (first/rest/end c))
       (lsb (bfr-or af bf cf))
       ((when (and aend bend cend))
        (bfr-sterm lsb))
       (rest (bfr-logior-sss ar br cr)))
    (bfr-scons lsb rest)))

(defsymbolic bfr-lognor-ss ((a s)
                            (b s))
  :returns (nor s (lognor a b))
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b))
       (lsb (bfr-nor af bf))
       ((when (and aend bend))
        (bfr-sterm lsb))
       (rest (bfr-lognor-ss ar br)))
    (bfr-scons lsb rest)))

(defsymbolic bfr-lognand-ss ((a s)
                             (b s))
  :returns (nand s (lognand a b))
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b))
       (lsb (bfr-nand af bf))
       ((when (and aend bend))
        (bfr-sterm lsb))
       (rest (bfr-lognand-ss ar br)))
    (bfr-scons lsb rest)))

(defsymbolic bfr-logandc1-ss ((a s)
                              (b s))
  :returns (andc1 s (logandc1 a b))
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b))
       (lsb (bfr-andc1 af bf))
       ((when (and aend bend))
        (bfr-sterm lsb))
       (rest (bfr-logandc1-ss ar br)))
    (bfr-scons lsb rest)))

(defsymbolic bfr-logandc2-ss ((a s)
                              (b s))
  :returns (andc2 s (logandc2 a b))
  :measure (+ (len a) (len b))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b))
       (lsb (bfr-andc2 af bf))
       ((when (and aend bend))
        (bfr-sterm lsb))
       (rest (bfr-logandc2-ss ar br)))
    (bfr-scons lsb rest)))

(defsection sv::aig-symbolic-arithmetic
  :parents (sv::bit-blasting)
  :short "A more or less complete set of functions for doing arithmetic on a
symbolic bitvector representation consisting of lists of AIGs."
  :long "<p>See @(see gl::symbolic-arithmetic).  This is almost the same, but
for AIGs instead of for @(see gl::bfr)s.</p>")

(xdoc::change-base-pkg sv::aig-symbolic-arithmetic "SV")

(local (xdoc::set-default-parents sv::aig-symbolic-arithmetic))

; Frustratingly, we can't quite reuse gl/symbolic-arithmetic because it does
; its computations in terms of BFRs, i.e., it will do either AIG or BDD
; operations depending on the current attachment to BFR-MODE.  But we need to
; be able to do these with AIGs even in the midst of a GL BDD proof --
; unfortunate.

; In order to reuse the formulations & proofs we've already done in
; gl/symbolic-arithmetic, this book uses a hack -- in symbolic-arithmetic, we
; record in a table the defsymbolic events that we use to create these
; bfr-based functions and their correctness proofs.  We then replicate the
; events here, basically replacing occurrences of "BFR-" with "AIG-".  Very
; ugly, but, we hope, effective.



(define sv::aig-i2v ((x integerp))
  :returns (aig)
  :short "Like @(see gl::i2v) but for AIGs only."
  :measure (integer-length x)
  :prepwork ((local (in-theory (enable acl2::integer-length**))))
  (cond ((zip x) nil)
        ((eql x -1) '(t))
        (t (sv::aig-scons (logbitp 0 x)
                          (sv::aig-i2v (logcdr x)))))
  ///
  (defthm aig-i2v-correct
    (equal (sv::aig-list->s (sv::aig-i2v x) env)
           (ifix x))
    :hints(("Goal" :in-theory (enable gl::bfr-snorm)))))


(defun defsymbolic-formals-pair-with-evals-aig (x)
  (if (atom x)
      nil
    (cons (cons (caar x)
                (case (cadar x)
                  (n `(nfix ,(caar x)))
                  (i `(ifix ,(caar x)))
                  (p `(acl2::pos-fix ,(caar x)))
                  (b `(sv::aig-eval ,(caar x) env))
                  (u `(sv::aig-list->u ,(caar x) env))
                  (s `(sv::aig-list->s ,(caar x) env))))
          (defsymbolic-formals-pair-with-evals-aig (cdr x)))))

(defun defsymbolic-return-specs-aig (x formal-evals)
  (if (atom x)
      nil
    (append (case (cadar x)
              ((n i p) (and (third (car x))
                            `((equal ,(caar x)
                                     ,(sublis formal-evals (third (car x)))))))
              (b `((equal (sv::aig-eval ,(caar x) env)
                          ,(sublis formal-evals (third (car x))))))
              (u `((equal (sv::aig-list->u ,(caar x) env)
                          ,(sublis formal-evals (third (car x))))))
              (s `((equal (sv::aig-list->s ,(caar x) env)
                          ,(sublis formal-evals (third (car x)))))))
            (defsymbolic-return-specs-aig (cdr x) formal-evals))))

;; (defmacro sv::aig-and* (&rest args)
;;   (xxxjoin 'sv::aig-and args))

;; (defmacro sv::aig-or* (&rest args)
;;   (xxxjoin 'sv::aig-or args))

(table bfr-aig-subst nil
       ;; This is a substitution for functional instantiation
       '((bfr-list->u    . sv::aig-list->u)
         (bfr-list->s    . sv::aig-list->s)
         (bfr-eval       . acl2::aig-eval)
         (bfr-ite-fn     . (lambda (x y z) (acl2::aig-ite x y z)))
         (bfr-binary-and . (lambda (x y) (acl2::aig-and x y)))
         (bfr-binary-or  . (lambda (x y) (acl2::aig-or x y)))
         (bfr-not        . (lambda (x) (acl2::aig-not x)))
         (bfr-xor        . (lambda (x y) (acl2::aig-xor x y)))
         (bfr-iff        . (lambda (x y) (acl2::aig-iff x y)))
         (bfr-nor        . (lambda (x y) (acl2::aig-nor x y)))
         (bfr-nand       . (lambda (x y) (acl2::aig-nand x y)))
         (bfr-andc1      . (lambda (x y) (acl2::aig-andc1 x y)))
         (bfr-andc2      . (lambda (x y) (acl2::aig-andc2 x y))))
       :clear)

(defun bfr-aig-functional-subst (world)
  (let ((alist (table-alist 'bfr-aig-subst world)))
    (pairlis$ (strip-cars alist) (pairlis$ (strip-cdrs alist) nil))))

(local #!acl2
       (defthm aig-ite-of-const-conditions
         (and (equal (aig-ite t y z) y)
              (equal (aig-ite nil y z) z))
         :hints(("Goal" :in-theory (enable aig-ite aig-and aig-or aig-not)))))

(local (def-ruleset! defsymbolic-aig-functions nil))

(defun defsymbolic-aig-fn (name args subst)
  (declare (xargs :mode :program))
  (b* (((mv & args)
        (acl2::template-subst-rec args
                                  (acl2::make-tmplsubst :atoms subst
                                                        :strs '(("BFR" "AIG" . sv::pkg))
                                                        :pkg-sym 'sv::pkg)))
       ((mv kwd-alist other-kws other-args)
        (extract-some-keywords
         '(:spec :returns :correct-hints :depends-hints :correct-hyp :abstract) args nil))
       ((unless (eql (len other-args) 2))
        (er hard? 'defsymbolic-fn "Need formals and body in addition to keyword args"))
       (formals (car other-args))
       (body (cadr other-args))
       (returns (cdr (assoc :returns kwd-alist)))
       ((unless (consp returns))
        (er hard? 'defsymbolic-aig-fn "Need a returns list"))
       (returns (if (eq (car returns) 'mv)
                    (cdr returns)
                  (list returns)))
       (- (defsymbolic-check-formals formals))
       (- (defsymbolic-check-returns returns))
       ((when (intersectp-eq (strip-cars formals)
                             (strip-cars returns)))
        (er hard? 'defsymbolic-aig-fn "Formals and returns overlap"))
       (return-binder (if (consp (cdr returns))
                          `(mv . ,(strip-cars returns))
                        (caar returns)))
       (formal-vars (strip-cars formals))
       (exec-name (acl2::tmpl-sym-sublis '(("BFR" "AIG" . sv::pkg)) name 'sv::pkg))
       (abstractp (std::getarg :abstract nil kwd-alist))
       (old-exec-name (if abstractp
                          (intern-in-package-of-symbol
                           (concatenate 'string (symbol-name name) "-EXEC")
                           name)
                        name))
       (old-correct (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name old-exec-name) "-CORRECT")
                     old-exec-name)))
    `(progn
       (define ,exec-name ,(defsymbolic-define-formals formals)
         ,@other-kws
         :returns ,(defsymbolic-define-returns returns)
         :progn t
         ,body
         ///
         (table bfr-aig-subst ',old-exec-name ',exec-name)

         (defthm ,(intern-in-package-of-symbol
                   (concatenate 'string (symbol-name exec-name) "-CORRECT")
                   exec-name)
           (b* ((,return-binder (,exec-name . ,formal-vars)))
             ,(let ((concl `(and . ,(defsymbolic-return-specs-aig returns
                                      (defsymbolic-formals-pair-with-evals-aig formals))))
                    (correct-hyp (cdr (assoc :correct-hyp kwd-alist))))
                (if correct-hyp
                    `(implies ,correct-hyp ,concl)
                  concl)))
           :hints ((let ((subst (bfr-aig-functional-subst world)))
                     `(:use ((:functional-instance
                              ,',old-correct
                              (bfr-mode (lambda () t))
                              . ,subst))))
                   (and stable-under-simplificationp
                        '(:in-theory (enable* defsymbolic-aig-functions
                                              sv::aig-list->s
                                              sv::aig-list->u))))))
       (local (in-theory (disable ,exec-name)))
       (local (add-to-ruleset defsymbolic-aig-functions ,exec-name)))))

(defun defsymbolic-aig-table-events (table acc subst)
  (declare (xargs :mode :program))
  (if (atom table)
      acc
    (defsymbolic-aig-table-events (cdr table)
      (cons (defsymbolic-aig-fn (caar table) (cdar table) subst) acc)
      subst)))

(defmacro sv::aig-ite-bvv (c v1 v0)
  `(let ((sv::aig-ite-bvv-test ,c))
     (if sv::aig-ite-bvv-test
         (if (eq sv::aig-ite-bvv-test t)
             ,v1
           (sv::aig-ite-bvv-fn sv::aig-ite-bvv-test ,v1 ,v0))
       ,v0)))

(defmacro sv::aig-ite-bss (c v1 v0)
  `(let ((sv::aig-ite-bss-test ,c))
     (if sv::aig-ite-bss-test
         (if (eq sv::aig-ite-bss-test t)
             ,v1
           (sv::aig-ite-bss-fn sv::aig-ite-bss-test ,v1 ,v0))
       ,v0)))


(local (defmacro no-op-event (&rest args)
         (declare (ignore args))
         '(progn)))

(local (in-theory (e/d* (bitops::ihsext-redefs
                         bitops::ihsext-inductions))))


(local (defthm integer-length-bound-s-correct-aig
         (< (integer-length (sv::aig-list->s x env))
            (integer-length-bound-s x))
         :hints(("Goal" :in-theory (enable integer-length-bound-s)))
         :rule-classes :linear))

(defthm integer-length-bound-s-correct-aig
  (< (integer-length (sv::aig-list->s x env))
     (integer-length-bound-s x))
  :hints(("Goal" :in-theory (enable integer-length-bound-s)))
  :rule-classes :linear)

(defmacro sv::aig-ite* (x y z)
  (cond ((and (or (quotep y) (atom y))
              (or (quotep z) (atom z)))
         `(sv::aig-ite ,x ,y ,z))
        (t
         `(mbe :logic (sv::aig-ite ,x ,y ,z)
               :exec (let ((sv::aig-ite-x-do-not-use-elsewhere ,x))
                       (cond
                        ((eq sv::aig-ite-x-do-not-use-elsewhere nil) ,z)
                        ((eq sv::aig-ite-x-do-not-use-elsewhere t) ,y)
                        (t
                         (sv::aig-ite sv::aig-ite-x-do-not-use-elsewhere
                                        ,y ,z))))))))

(encapsulate nil
  (make-event
   (cons 'progn
         (defsymbolic-aig-table-events
           (table-alist 'defsymbolic-forms (w state)) nil
           '((bfr-list->u    . sv::aig-list->u)
             (bfr-list->s    . sv::aig-list->s)
             (bfr-ite-fn     . acl2::aig-ite-fn)
             (bfr-ite        . acl2::aig-ite)
             (bfr-eval       . acl2::aig-eval)
             (bfr-binary-and . acl2::aig-and)
             (bfr-binary-or  . acl2::aig-or)
             (bfr-and        . acl2::aig-and)
             (bfr-or         . acl2::aig-or)
             (bfr-not        . acl2::aig-not)
             (bfr-xor        . acl2::aig-xor)
             (bfr-iff        . acl2::aig-iff)
             (bfr-nor        . acl2::aig-nor)
             (bfr-nand       . acl2::aig-nand)
             (bfr-andc1      . acl2::aig-andc1)
             (bfr-andc2      . acl2::aig-andc2)
             (add-bfr-pat    . no-op-event))))))
