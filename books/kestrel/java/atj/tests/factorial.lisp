; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../implementation" :ttags (:open-input-channel (:oslib) (:quicklisp) :quicklisp.osicat))

(include-book "../types-for-natives")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Factorial function.

(defun fact (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      1
    (* n (fact (1- n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests for the factorial function.

(defconst *fact-tests*
  '(("Factorial0" (fact 0))
    ("Factorial1" (fact 1))
    ("Factorial10" (fact 10))
    ("Factorial100" (fact 100))
    ("Factorial1000" (fact 1000))
    ("Factorial10000" (fact 10000))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the factorial function, with testing code.

(java::atj fact
           :deep t
           :guards nil
           :java-class "FactorialDeep"
           :tests *fact-tests*)

(java::atj fact
           :deep t
           :guards t
           :java-class "FactorialDeepUnderGuards"
           :tests *fact-tests*)

(java::atj fact
           :deep nil
           :guards nil
           :java-class "FactorialShallow"
           :tests *fact-tests*)

(java::atj fact
           :deep nil
           :guards t
           :java-class "FactorialShallowUnderGuards"
           :tests *fact-tests*)