; Arithmetic-2 Library
; Copyright (C) 1999 Robert Krug <rkrug@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; integerp.lisp
;;;
;;;
;;; This book contains several lemmatta about when a sum or
;;; product is or is not an integer.
;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../pass1/top"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; The first two cannot be type-prescriptions.

(defthm integerp-1a
  (implies (and (integerp (+ x y))
		(acl2-numberp x)
		(integerp y))
	   (integerp x)))

(defthm integerp-1b
  (implies (and (integerp (+ x y))
		(acl2-numberp y)
		(integerp x))
	   (integerp y)))

; The next eight rules are rather weak, and do not cover all the cases.
; Perhaps I should do something about it.

(defthm nintegerp-1a
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(< x y))
	   (not (integerp (* x (/ y)))))
  :hints (("Goal" :use (:theorem
			(implies (and (real/rationalp x)
				      (real/rationalp y)
				      (< 0 x)
				      (< x y))
				 (and (< 0 (* x (/ y)))
				      (< (* x (/ y)) 1))))
                  :in-theory (enable prefer-*-to-/)))
  :rule-classes :type-prescription)

(defthm nintegerp-1b
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(< x y))
	   (not (integerp (* (/ y) x))))
  :rule-classes :type-prescription)

(defthm nintegerp-2a
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(< y x))
	   (not (integerp (* x (/ y)))))
  :hints (("Goal" :use (:instance nintegerp-1a
				  (x (- x))
				  (y (- y)))))
  :rule-classes :type-prescription)

(defthm nintegerp-2b
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(< y x))
	   (not (integerp (* (/ y) x))))
  :rule-classes :type-prescription)

(defthm nintegerp-3a
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(< y (- x)))
	   (not (integerp (* x (/ y)))))
  :hints (("Goal" :use (:instance nintegerp-1a
				  (y (- y)))))
  :rule-classes :type-prescription)

(defthm nintegerp-3b
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< 0 x)
		(< y (- x)))
	   (not (integerp (* (/ y) x))))
  :rule-classes :type-prescription)

(defthm nintegerp-4a
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(< (- x) y))
	   (not (integerp (* x (/ y)))))
  :hints (("Goal" :use (:instance nintegerp-1a
				  (x (- x)))))
  :rule-classes :type-prescription)

(defthm nintegerp-4b
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(< x 0)
		(< (- x) y))
	   (not (integerp (* (/ y) x))))
  :rule-classes :type-prescription)

(encapsulate
 ()

 (local
  (defthm nintegerp-expt-helper
    (implies (and (< 1 x)
		  (real/rationalp x)
		  (< n 0)
		  (integerp n))
	     (and (< 0 (expt x n))
		  (< (expt x n) 1)))
    :rule-classes nil))

 (defthm nintegerp-expt
   (implies (and (real/rationalp x)
		 (< 1 x)
		 (integerp n)
		 (< n 0))
	    (not (integerp (expt x n))))
   :hints (("Goal" :use nintegerp-expt-helper))
   :rule-classes :type-prescription)

 (defthm nintegerp-/
   (implies (and (real/rationalp x)
		 (< 1 x))
	    (not (integerp (/ x))))
   :hints (("Goal" :use ((:instance nintegerp-expt
				    (n -1)))
	           :in-theory (disable nintegerp-expt)))
  :rule-classes :type-prescription)
)
