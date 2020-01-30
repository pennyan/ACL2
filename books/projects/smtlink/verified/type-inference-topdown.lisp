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

(include-book "typed-term")

(define look-up-judge-list ((term-lst pseudo-term-listp)
                            (judge pseudo-termp)
                            (supertype type-to-types-alist-p))
  :returns (jugde-lst pseudo-term-listp)
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       (judge (pseudo-term-fix judge))
       (supertype (type-to-types-alist-fix supertype))
       ((unless (consp term-lst)) nil)
       ((cons term-hd term-tl) term-lst)
       (judge-hd (look-up-path-cond term-hd judge supertype))
       ((unless (is-conjunct? judge-hd))
        (er hard? 'type-inference-topdpwn=>look-up-judge-list
            "~p0 is not a conjunct.~%" judge-hd)))
    (cons judge-hd (look-up-judge-list term-tl judge supertype))))

(local (in-theory (disable (:executable-counterpart typed-term)
                           (:executable-counterpart typed-term-list))))

(encapsulate ()
  (local
   (in-theory (disable symbol-listp
                       pseudo-term-listp-of-symbol-listp
                       acl2::symbol-listp-when-not-consp
                       acl2::pseudo-termp-opener
                       acl2-count)))

(define choose-judge-helper ((judges pseudo-termp)
                             (term pseudo-termp)
                             (supertype type-to-types-alist-p)
                             (acc pseudo-termp)
                             (counter natp))
  :guard (is-conjunct-list? acc term supertype)
  :returns (mv (ctr natp)
               (judge (and (pseudo-termp judge)
                           (is-conjunct-list? judge term supertype))
                      :hyp :guard))
  :measure (acl2-count (pseudo-term-fix judges))
  :verify-guards nil
  (b* ((judges (pseudo-term-fix judges))
       (term (pseudo-term-fix term))
       (acc (pseudo-term-fix acc))
       ((unless (mbt (is-conjunct-list? acc term supertype)))
        (mv 0 ''t))
       (counter (nfix counter))
       ((if (equal judges ''t)) (mv counter acc))
       ((if (and (type-predicate-of-term judges term supertype)
                 (zp counter)))
        (mv (1+ counter)
            `(if ,judges ,acc 'nil)))
       ((if (and (type-predicate-of-term judges term supertype)
                 (not (zp counter))))
        (mv counter acc))
       ((unless (is-conjunct? judges))
        (prog2$ (er hard? 'type-inference-topdown=>choose-judge
                    "Judges should be a conjunct: ~q0" judges)
                (mv counter acc)))
       ((list & cond then &) judges)
       ((mv new-ctr new-acc)
        (choose-judge-helper cond term supertype acc counter)))
    (choose-judge-helper then term supertype new-acc new-ctr)))

(verify-guards choose-judge-helper)
)

(define choose-judge ((judges pseudo-termp)
                      (term pseudo-termp)
                      (supertype type-to-types-alist-p))
  :returns (judge (and (pseudo-termp judge)
                       (is-conjunct-list? judge term supertype))
                  :hyp :guard)
  (b* (((mv & judge)
        (choose-judge-helper judges term supertype ''t 0)))
    judge))

;;----------------------------------------------------------------

(define unify-variable ((tterm typed-term-p)
                        (expected pseudo-termp)
                        (options type-options-p))
  :guard (and (good-typed-term-p tterm options)
              (equal (typed-term->kind tterm) 'variablep))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options))
                   :hints (("Goal"
                            :in-theory (enable good-typed-variable-p))))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (pseudo-termp expected)
                          (equal (typed-term->kind tterm) 'variablep)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((type-options to) options)
       ((unless (is-conjunct-list? expected tt.term to.supertype))
        (prog2$
         (er hard? 'type-inference-topdown=>unify-variable
             "Expected ~p0 is not a conjunct list.~%" expected)
         (make-typed-term)))
       ((unless (equal expected ''t))
        (make-typed-term :term tt.term
                         :path-cond tt.path-cond
                         :judgements expected)))
    (make-typed-term :term tt.term
                     :path-cond tt.path-cond
                     :judgements (choose-judge tt.judgements tt.term
                                               to.supertype))))

(define unify-quote ((tterm typed-term-p)
                     (expected pseudo-termp)
                     (options type-options-p))
  :guard (and (good-typed-term-p tterm options)
              (equal (typed-term->kind tterm) 'quotep))
  :returns (new-tt (and (typed-term-p new-tt)
                        (good-typed-term-p new-tt options))
                   :hints (("Goal"
                            :in-theory (enable good-typed-quote-p))))
  (b* (((unless (mbt (and (typed-term-p tterm)
                          (pseudo-termp expected)
                          (type-options-p options)
                          (equal (typed-term->kind tterm) 'quotep)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((typed-term tt) tterm)
       ((type-options to) options)
       ((unless (is-conjunct-list? expected tt.term to.supertype))
        (prog2$
         (er hard? 'type-inference-topdown=>unify-variable
             "Expected ~p0 is not a conjunct list.~%" expected)
         (make-typed-term)))
       ((unless (equal expected ''t))
        (make-typed-term :term tt.term
                         :path-cond tt.path-cond
                         :judgements expected)))
    (make-typed-term :term tt.term
                     :path-cond tt.path-cond
                     :judgements (choose-judge tt.judgements tt.term
                                               to.supertype))))
stop...now I have to think

(defines unify-type
  :well-founded-relation l<
  :verify-guards nil

  (define unify-fncall ((tterm typed-term-p)
                        (expected pseudo-termp)
                        (options type-options-p)
                        state)
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'fncallp))
    :returns (new-tt (and (typed-term-p new-tt)
                          (good-typed-term-p new-tt options)))
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (pseudo-termp expected)
                            (equal (typed-term->kind tterm) 'fncallp)
                            (good-typed-term-p tterm options))))
          (make-typed-term))
         ((type-options to) options)
         ((typed-term tt) tterm)
         ((typed-term tt-top) (typed-term->top tt to))
         (judge-top (if (equal expected ''t)
                        (choose-judge tt-top.judgements tt-top.term
                                      to.supertype)
                      expected))
         (new-top (make-typed-term :term tt-top.term
                                   :path-cond tt-top.path-cond
                                   :judgements judge-top))
         (extended-top (extend-judgements-rev judge-top tt.path-cond to state))
         ((cons fn actuals) tt.term)
         (conspair (assoc-equal fn to.functions))
         ((unless conspair)
          (er hard? 'type-inference-topdown=>unify-fncall
              "There exists no function description for function ~p0. ~%" fn))
         (fn-description (cdr conspair))
         (expected-actuals (returns-judgement-rev fn actuals ...))
         (new-actuals
          (unify-type-list
           (typed-term-fncall->actuals tt to) expected-actuals to state)))
      (make-typed-fncall new-top new-actuals)))

  (define unify-lambda ((tterm typed-term-p)
                        (expected pseudo-termp)
                        (options type-options-p)
                        state)
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'lambdap))
    :returns (new-tt (and (typed-term-p new-tt)
                          (good-typed-term-p new-tt options)))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (equal (typed-term->kind tterm) 'lambdap)
                            (good-typed-term-p tterm options))))
          (make-typed-term))
         ((type-options to) options)
         ((typed-term tt) tterm)
         ((typed-term tt-actuals) (typed-term-lambda->actuals tt to))
         ((typed-term tt-body) (typed-term-lambda->body tt to))
         ((typed-term tt-top) (typed-term->top tt to))
         (judge-top (if (equal expected ''t)
                        (choose-judge tt-top.judgements tt-top.term
                                      to.supertype)
                      expected))
         (new-top (make-typed-term :term tt-top.term
                                   :path-cond tt-top.path-cond
                                   :judgements judge-top))
         (body-expected
          (term-substitution judge-top tt-top.term tt-body.term t))
         (new-body (unify-type tt-body body-expected to state))
         ((typed-term nbd) new-body)
         (formals (lambda-formals (car tt-top.term)))
         (actuals (cdr tt-top.term))
         (formals-judges
          (look-up-judge-list formals nbd.judgements to.supertype))
         (actuals-expected
          (term-substitution-linear formals-judges formals actuals t))
         (new-actuals (unify-type-list tt-actuals actuals-expected options state)))
      (make-typed-lambda new-top new-body new-actuals to)))

  (define unify-if ((tterm typed-term-p)
                    (expected pseudo-termp)
                    (options type-options-p)
                    state)
    :guard (and (good-typed-term-p tterm options)
                (equal (typed-term->kind tterm) 'ifp))
    :returns (new-tt (and (typed-term-p new-tt)
                          (good-typed-term-p new-tt options)))
    :measure (list (acl2-count (typed-term->term tterm)) 0)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (pseudo-termp expected)
                            (type-options-p options)
                            (equal (typed-term->kind tterm) 'ifp)
                            (good-typed-term-p tterm options))))
          (make-typed-term))
         ((type-options to) options)
         ((typed-term tt) tterm)
         ((typed-term tt-cond) (typed-term-if->cond tt to))
         ((typed-term tt-then) (typed-term-if->then tt to))
         ((typed-term tt-else) (typed-term-if->else tt to))
         ((typed-term tt-top) (typed-term->top tt to))
         (new-cond (unify-type tt-cond ''t to state))
         (judge-top (if (equal expected ''t)
                        (choose-judge tt-top.judgements tt-top.term
                                      to.supertype)
                      expected))
         (new-top (make-typed-term :term tt-top.term
                                   :path-cond tt-top.path-cond
                                   :judgements judge-top))
         (then-expected (term-substitution judge-top tt-top.term tt-then.term t))
         (new-then (unify-type tt-then then-expected to state))
         (else-expected (term-substitution judge-top tt-top.term tt-else.term t))
         (new-else (unify-type tt-else else-expected to state)))
      (make-typed-if new-top new-cond new-then new-else to)))

  (define unify-type ((tterm typed-term-p)
                      (expected pseudo-termp)
                      (options type-options-p)
                      state)
    :guard (good-typed-term-p tterm options)
    :returns (new-tt (and (typed-term-p new-tt)
                          (good-typed-term-p new-tt options)))
    :measure (list (acl2-count (typed-term->term tterm)) 1)
    (b* (((unless (mbt (and (typed-term-p tterm)
                            (type-options-p options)
                            (pseudo-termp expected)
                          (good-typed-term-p tterm options))))
        (make-typed-term))
       ((if (equal (typed-term->kind tterm) 'variablep))
        (unify-variable tterm expected options state))
       ((if (equal (typed-term->kind tterm) 'quotep))
        (unify-quote tterm expected options state))
       ((if (equal (typed-term->kind tterm) 'lambdap))
        (unify-lambda tterm expected options state))
       ((if (equal (typed-term->kind tterm) 'ifp))
        (unify-if tterm expected options state)))
    (unify-fncall tterm expected options state)))

  (define unify-type-list ((tterm-lst typed-term-list-p)
                           (expected-lst pseudo-term-listp)
                           (options type-options-p)
                           state)
  :returns (new-ttl (and (typed-term-list-p new-ttl)
                         (good-typed-term-list-p new-ttl options)))
  :guard (good-typed-term-list-p tterm-lst options)
  :measure (list (acl2-count (typed-term-list->term-lst tterm-lst))
                 1)
  (b* (((unless (mbt (and (typed-term-list-p tterm-lst)
                          (type-options-p options)
                          (pseudo-term-listp expected-lst)
                          (good-typed-term-list-p tterm-lst options))))
        (make-typed-term-list))
       ((typed-term-list ttl) tterm-lst)
       ((unless (typed-term-list-consp ttl)) ttl)
       ((unless (consp expected-lst))
        (prog2$
         (er hard? 'type-inference-topdown=>unify-type-list
             "Expected-lst is already empty while there are still ~
             typed-terms.~%")
         (make-typed-term-list)))
       ((cons expected-hd expected-tl) expected-lst))
    (typed-term-list->cons (unify-type (typed-term-list->car ttl options)
                                       expected-hd options state)
                           (unify-type-list (typed-term-list->cdr ttl options)
                                            expected-tl options state)
                           options)))
)

(verify-guards unify-type)
