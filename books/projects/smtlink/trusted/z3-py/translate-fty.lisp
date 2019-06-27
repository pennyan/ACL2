;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (23rd May, 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "../../verified/basics")
(include-book "./datatypes")

(defsection SMT-translate-fty
  :parents (z3-py)
  :short "Translating FTY declarations"

  (local (in-theory (enable string-or-symbol-p)))

  (define translate-bool ((b booleanp) (nil-type symbolp))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (enable paragraphp wordp))))
    (cond
     ;; Boolean: nil
     ((and (equal b nil)
           (equal nil-type nil))
      (list "False"))
     ;; A fty nil
     ((equal b nil)
      (list (str::downcase-string (concatenate 'string (lisp-to-python-names
                                                        nil-type) ".nil"))))
     ;; Boolean: t
     (t (list "True"))))

  (define translate-symbol ((sym symbolp))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (enable paragraphp wordp))))
    (str::downcase-string (lisp-to-python-names sym))
    ///
    (more-returns
     (translated
      (stringp translated)
      :name stringp-of-translate-symbol)))

  (define translate-fty-types ((fixtypes smt-fixtype-list-p)
                               (int-to-rat booleanp))
    :returns (translated paragraphp)
    :ignore-ok t
    nil)
  )
