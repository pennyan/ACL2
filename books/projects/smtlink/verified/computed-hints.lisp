;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

;;
;; This book defines a computed hint that looks for the function
;; "SMT-please"

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "clause-processors/just-expand" :dir :system)

(include-book "hint-interface")

(defsection SMT-computed-hints
  :parents (verified)
  :short "Define Smtlink computed-hints"

  ;; current tag . next computed-hint
  (defconst *SMT-computed-hints-table*
    '((process-hint . expand-hint)
      (expand-hint . smtlink-cp-w/-in-theory)
      (fix-hint . smtlink-cp-w/-in-theory)
      (smt-hint . nil)
      (fixed-hint . nil)
      (main-hint . nil)
      (A-hint . nil)))

  ;; verified version of split-kwd-alist
  (define my-split-kwd-alist ((key symbolp)
                              (kwd-alist true-listp))
    :returns (mv (pre true-listp)
                 (post true-listp))
    :measure (len kwd-alist)
    :hints (("Goal" :in-theory (disable true-list-fix-preserve-length)
             :use ((:instance true-list-fix-preserve-length
                              (x kwd-alist)))))
    (b* ((kwd-alist (true-list-fix kwd-alist))
         ((unless (consp kwd-alist)) (mv nil nil))
         ((if (eq key (car kwd-alist)))
          (mv nil kwd-alist))
         ((unless (consp (cdr kwd-alist)))
          (prog2$ (er hard? 'SMT-computed-hints=>my-split-kwd-alist "Something ~
  is wrong with the kwd-alist: ~q0" kwd-alist)
                  (mv nil nil)))
         ((mv pre post)
          (my-split-kwd-alist key (cddr kwd-alist))))
      (mv (cons (car kwd-alist)
                (cons (cadr kwd-alist)
                      pre))
          post)))

  (define treat-in-theory-hint ((enabled true-listp)
                                (kwd-alist true-listp))
    :returns (new-kwd-alist
              true-listp
              :hints (("Goal"
                       :in-theory (disable
                                   true-listp-of-my-split-kwd-alist.post)
                       :use ((:instance
                              true-listp-of-my-split-kwd-alist.post
                              (key :in-theory)
                              (kwd-alist (true-list-fix kwd-alist)))))))
    :guard-debug t
    (b* ((kwd-alist (true-list-fix kwd-alist))
         ((mv pre post)
          (my-split-kwd-alist :in-theory kwd-alist)))
      (cond ((and (consp post)
                  (consp (cdr post))
                  (consp (cadr post))
                  (equal (caadr post) 'enable))
             `(,@pre
               :in-theory (enable ,@enabled ,@(cdadr post))
               ,@(cddr post)))
            ((and (consp post)
                  (consp (cdr post))
                  (consp (cadr post))
                  (equal (caadr post) 'disable))
             `(,@pre
               :in-theory (e/d ,enabled (,@(cdadr post)))
               ,@(cddr post)))
            ((and (consp post)
                  (consp (cdr post))
                  (consp (cadr post))
                  (consp (cdadr post))
                  (consp (cddadr post))
                  (equal (caadr post) 'e/d))
             `(,@pre
               :in-theory (e/d (,@enabled ,@(car (cdadr post)))
                               (,@(cadr (cdadr post))))
               ,@(cddr post)))
            (t `(;; :do-not '(preprocess)
                 :in-theory (enable ,@enabled)
                            ,@kwd-alist
                            )))))

  (program)
  (define extract-hint-wrapper (cl)
    (cond ((endp cl) (mv nil nil nil))
          (t (b* ((lit cl))
               (case-match lit
                 ((('hint-please ('quote kwd-alist) ('quote tag)) . term)
                  (mv term kwd-alist tag))
                 (& (extract-hint-wrapper (cdr cl))))))))

  (define ch-replace (next-stage)
    (if (equal next-stage nil)
        nil
      `((,next-stage clause))))

  (define smtlink-cp-w/-in-theory (cl)
    (b* (((mv & kwd-alist tag) (extract-hint-wrapper cl))
         (next-stage (cdr (assoc tag *SMT-computed-hints-table*)))
         (ch-replace-hint (ch-replace next-stage))
         (rest-hint (treat-in-theory-hint '(hint-please) kwd-alist)))
      `(:computed-hint-replacement
        ,ch-replace-hint
        ,@rest-hint)))

  (define SMT-process-hint (cl
                            ;;flg
                            )
    (b* (((mv & kwd-alist tag) (extract-hint-wrapper cl))
         (next-stage (cdr (assoc tag *SMT-computed-hints-table*)))
         ;; ((unless flg) nil)
         )
      `(:computed-hint-replacement
        ,(ch-replace next-stage)
        ;; :do-not '(preprocess)
        ,@kwd-alist)))

  (logic)

  )
;; Add this line to your code to add a default hint of Smtlink
;; (add-default-hints '((SMT-computed-hint clause stable-under-simplificationp)))
;; Remove hint:
;; (remove-default-hints '((SMT-computed-hint clause stable-under-simplificationp)))
