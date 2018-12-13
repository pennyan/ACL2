;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (Dec 12 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "tools/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "hint-interface")

(set-state-ok t)

(defsection SMT-evil-cp
  :parents (trusted)
  :short "The evil trusted clause processor, will be removed in the future"

  (define evil-prove ((term pseudo-termp)
                      (smtlink-hint smtlink-hint-p))
    :returns (res booleanp)
    :ignore-ok t
    t)

  (defstub evil-prove-stub (term smtlink-hint) t)

  (program)

  (defttag :my-cl-proc)

  (progn
    (progn!

     (set-raw-mode-on state)

     (defun evil-prove-stub (term smtlink-hint)
       (evil-prove term smtlink-hint)))

    (define evil-cp ((cl pseudo-term-listp)
                     (smtlink-hint))
      (b* ((- (cw "Evil clause processor at your service!~%"))
           (res (evil-prove-stub (disjoin cl) smtlink-hint)))
        (if res
            (prog2$ (cw "Proved! Evil clause processor is glad to help!~%")
                    nil)
          (prog2$ (cw "~|~%NOTE: Unable to prove goal with ~
                  my-clause-processor and indicated hint.~|")
                  (list cl)))))

    (push-untouchable evil-prove t)
    )

  (define-trusted-clause-processor
    evil-cp
    nil
    :ttag Smtlink)
  )
