; A lightweight book of theorems about subrange.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "subrange-def")
(local (include-book "nthcdr"))
(local (include-book "cons"))
(local (include-book "nth"))
(local (include-book "len"))
(local (include-book "take"))
(local (include-book "append"))
(local (include-book "true-list-fix"))

(defthm true-listp-of-subrange-type-prescription
  (true-listp (subrange start end lst))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable subrange))))

;todo: only needed by axe?
(defthm true-listp-of-subrange
  (true-listp (subrange start end vals)))

(defthm subrange-out-of-order
  (implies (and (< end start)
                (integerp end)
                (integerp start))
           (equal (subrange start end lst)
                  nil))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm subrange-out-of-order-cheap
  (implies (and (syntaxp (and (quotep start)
                              (quotep end)))
                (< end start)
                (integerp end)
                (integerp start))
           (equal (subrange start end lst)
                  nil))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm car-of-subrange
  (implies (and (<= start end)
                (natp end))
           (equal (car (subrange start end lst))
                  (nth start lst)))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm cdr-of-subrange
  (implies (natp start)
           (equal (cdr (subrange start end lst))
                  (subrange (+ 1 start) end lst)))
  :hints (("Goal" :in-theory (enable subrange nthcdr-opener-alt))))

(defthm nthcdr-of-subrange
  (implies (and (natp start)
                (natp n)
                (integerp end))
           (equal (nthcdr n (subrange start end lst))
                  (subrange (+ start n) end lst)))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm consp-of-subrange
  (implies (and (natp start)
                (integerp end))
           (equal (consp (subrange start end lst))
                  (<= start end)))
  :hints (("Goal" :in-theory (enable subrange))))

(defthmd subrange-opener
  (implies (and (<= start end)
                (natp start)
                (integerp end))
           (equal (subrange start end lst)
                  (cons (nth start lst)
                        (subrange (+ 1 start) end lst)))))

(defthm subrange-iff
  (implies (integerp end)
           (iff (subrange start end x)
                (<= (nfix start) end)))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm len-of-subrange
  (implies (and (integerp end)
                (integerp start))
           (equal (len (subrange start end lst))
                  (if (< end (nfix start))
                      0
                    (+ 1 (- end (nfix start))))))
  :hints (("Goal" :in-theory (enable subrange take))))

(defthm subrange-same
  (implies (natp start)
           (equal (subrange start start lst)
                  (list (nth start lst))))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm subrange-of-0
  (equal (subrange 0 end lst)
         (take (+ 1 end) lst))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm subrange-is-all
  (implies (and (<= (+ -1 (len lst)) end)
                (natp end))
           (equal (subrange 0 end lst)
                  (take (+ 1 end) lst)))
  :hints (("Goal" :in-theory (enable subrange))))

;use a congruence?
(defthm subrange-of-true-list-fix
  (equal (subrange start end (true-list-fix lst))
         (subrange start end lst))
  :hints (("Goal" :in-theory (enable subrange))))

(defthmd take-of-nthcdr-becomes-subrange
  (implies (and (natp n2)
                (natp n1))
           (equal (take n1 (nthcdr n2 lst))
                  (subrange n2 (+ -1 n1 n2) lst)))
  :hints (("Goal" :in-theory (enable subrange))))

(theory-invariant (incompatible (:rewrite take-of-nthcdr-becomes-subrange) (:definition subrange)))

;rename take-of-subrange
(defthm take-of-subrange-gen
  (implies (and (<= i (+ 1 (- end start)))
                (natp start)
                (natp end)
                (natp i))
           (equal (take i (subrange start end lst))
                  (subrange start (+ start i -1) lst)))
  :hints (("Goal" :in-theory (e/d (subrange) (take-of-nthcdr-becomes-subrange)))))

(defthm subrange-out-of-order-or-singleton
  (implies (and (<= end start)
                (< end (len lst))
                (natp end)
                (integerp start))
           (equal (subrange start end lst)
                  (if (equal end start)
                      (list (nth start lst))
                    nil))))

(defthm nth-of-subrange
  (implies (and (integerp end)
                (natp start)
                (natp n))
           (equal (nth n (subrange start end lst))
                  (if (<= n (- end start))
                      (nth (+ n start) lst)
                    nil)))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm subrange-up-to-end-becomes-nthcdr
  (implies (and (equal len (len lst))
                (natp start) ;new
                )
           (equal (subrange start (+ -1 len) lst)
                  (true-list-fix (nthcdr start lst))))
  :hints (("Goal" :in-theory (e/d (subrange) (TAKE-OF-NTHCDR-BECOMES-SUBRANGE)))))

(defthmd subrange-up-to-end-becomes-nthcdr-strong
  (implies (and (equal k (+ -1 (len lst)))
                (natp start) ;new
                )
           (equal (subrange start k lst)
                  (true-list-fix (nthcdr start lst)))))

(defthm append-of-subrange-and-subrange-adjacent
  (implies (and (equal s2 (+ 1 e1))
                (< e2 (len lst))
                (<= s1 e1)
                (<= s2 e2)
                (natp e1)
                (natp s1)
                (natp s2)
                (natp e2))
           (equal (append (subrange s1 e1 lst) (subrange s2 e2 lst))
                  (subrange s1 e2 lst)))
  :hints (("Goal" :in-theory (enable equal-of-append))))

(defthm subrange-of-1-and-cons
  (implies (natp end)
           (equal (subrange 1 end (cons a x))
                  (subrange 0 (+ -1 end) x)))
  :hints (("Goal" :in-theory (enable subrange))))

(defthm equal-of-cdr-and-subrange-same
  (implies (and (< end (len lst))
                (natp end))
           (equal (equal (cdr lst) (subrange 1 end lst))
                  (and (true-listp lst)
                       (equal (len lst) (+ 1 end))))))

(defthmd equal-of-subrange-opener-helper
  (implies (and (natp low)
                (natp high)
                (<= low high))
           (equal (equal (subrange low high x)
                         y)
                  (and (consp y)
                       (equal (nth low x) (nth 0 y))
                       (equal (subrange (+ 1 low) high x)
                              (cdr y)))))
  :hints (("Goal" :use ((:instance subrange-opener (end high) (start low) (lst x))))))

(defthmd equal-of-subrange-opener
  (implies (and (syntaxp (and (quotep low)
                              (quote high)))
                (natp low)
                (natp high)
                (<= low high))
           (equal (equal (subrange low high x)
                         y)
                  (and (consp y)
                       (equal (nth low x) (nth 0 y))
                       (equal (subrange (+ 1 low) high x)
                              (cdr y)))))
  :hints (("Goal" :use (:instance equal-of-subrange-opener-helper))))

(defthm equal-subrange-nthcdr-rewrite
  (implies (and (equal (+ 1 j) (len x))
                (true-listp x))
           (equal (equal (subrange i j x)
                         (nthcdr i x))
                  t))
  :hints (("Goal" :in-theory (e/d (subrange nthcdr) ()))))
