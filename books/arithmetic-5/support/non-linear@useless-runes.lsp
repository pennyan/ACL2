(ARITH-ASSOCIATIVITY-OF-*)
(ARITH-COMMUTATIVITY-OF-* (5 3 (:REWRITE DEFAULT-*-2))
                          (5 3 (:REWRITE DEFAULT-*-1))
                          (4 4
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(ARITH-COMMUTATIVITY-2-OF-* (7 5 (:REWRITE DEFAULT-*-1))
                            (6 5 (:REWRITE DEFAULT-*-2))
                            (3 3
                               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                            (3 3 (:REWRITE FOLD-CONSTS-IN-*)))
(ARITH-UNICITY-OF-1 (3 3
                       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                    (2 1 (:REWRITE DEFAULT-*-2))
                    (1 1 (:REWRITE DEFAULT-*-1)))
(ARITH-TIMES-ZERO)
(ARITH-INVERSE-OF-*-1 (1 1 (:REWRITE DEFAULT-UNARY-/))
                      (1 1 (:REWRITE DEFAULT-*-2))
                      (1 1 (:REWRITE DEFAULT-*-1)))
(ARITH-INVERSE-OF-*-2 (3 3
                         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                      (2 1 (:REWRITE DEFAULT-*-2))
                      (1 1 (:REWRITE FOLD-CONSTS-IN-*))
                      (1 1 (:REWRITE DEFAULT-UNARY-/))
                      (1 1 (:REWRITE DEFAULT-*-1)))
(ARITH-INVERSE-OF-*-3 (3 3
                         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                      (2 1 (:REWRITE DEFAULT-*-2))
                      (1 1 (:REWRITE DEFAULT-UNARY-/))
                      (1 1 (:REWRITE DEFAULT-*-1)))
(ARITH-FUNCTIONAL-SELF-INVERSION-OF-/)
(ARITH-DISTRIBUTIVITY-OF-/-OVER-*)
(ARITH-FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT
     (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 3
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (3 2 (:REWRITE DEFAULT-*-2))
     (3 2 (:REWRITE DEFAULT-*-1)))
(ARITH-FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT
     (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 3
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (3 2 (:REWRITE DEFAULT-*-2))
     (3 2 (:REWRITE DEFAULT-*-1)))
(ARITH-RECIPROCAL-MINUSA)
(ARITH-DISTRIBUTIVITY-1 (7 5 (:REWRITE DEFAULT-*-2))
                        (6 5 (:REWRITE DEFAULT-*-1))
                        (5 5
                           (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                        (4 3 (:REWRITE DEFAULT-+-2))
                        (4 3 (:REWRITE DEFAULT-+-1)))
(ARITH-DISTRIBUTIVITY-2 (6 4 (:REWRITE DEFAULT-*-2))
                        (5 5
                           (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                        (5 4 (:REWRITE DEFAULT-*-1))
                        (4 3 (:REWRITE DEFAULT-+-2))
                        (4 3 (:REWRITE DEFAULT-+-1)))
(ARITH-FOLD-CONSTS-IN-*)
(ARITH-EXPT-0 (22 22
                  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-1))
              (22 22
                  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
              (22 22
                  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
              (22 22
                  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
              (4 4
                 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1))
              (4 4
                 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE<1))
              (4 4
                 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
              (4 4
                 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE<1))
              (2 2 (:REWRITE ZIP-OPEN))
              (2 2 (:LINEAR EXPT->-1-2))
              (2 2 (:LINEAR EXPT->-1-1))
              (2 2 (:LINEAR EXPT-<-1-2))
              (2 2 (:LINEAR EXPT-<-1-1))
              (1 1
                 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION)))
(ARITH-EXPT-1 (2 2
                 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
              (1 1
                 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
              (1 1
                 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE)))
(ARITH-EXPT-MINUS-1
     (44 24 (:REWRITE DEFAULT-<-2))
     (32 32
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (28 24 (:REWRITE DEFAULT-<-1))
     (16 4
         (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1))
     (16 4
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE<1))
     (16 4
         (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
     (16 4
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE<1))
     (15 15
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (15 15
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
     (15 15
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-2))
     (15 15
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-1))
     (15 15
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
     (15 15
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (15 15
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
     (9 3 (:REWRITE DEFAULT-UNARY-/))
     (8 2 (:LINEAR EXPT->-1-2))
     (8 2 (:LINEAR EXPT->-1-1))
     (8 2 (:LINEAR EXPT-<-1-2))
     (8 2 (:LINEAR EXPT-<-1-1))
     (3 2 (:REWRITE DEFAULT-*-1))
     (2 2 (:REWRITE DEFAULT-*-2))
     (1 1 (:REWRITE ARITH-INVERSE-OF-*-1)))
(ARITH-FUNCTIONAL-COMMUTATIVITY-OF-EXPT-/
     (6 6
        (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-2))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-1))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE)))
(ARITH-EXPT-MINUS-EXPONENT
     (647 647
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-1))
     (644 644
          (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (406 406
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (256 31 (:REWRITE DEFAULT-*-2))
     (200 190 (:REWRITE DEFAULT-<-2))
     (192 190 (:REWRITE DEFAULT-<-1))
     (86 28
         (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1))
     (86 28
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE<1))
     (86 28
         (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
     (86 28
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE<1))
     (52 52 (:REWRITE DEFAULT-+-2))
     (52 52 (:REWRITE DEFAULT-+-1))
     (46 46
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (43 14 (:LINEAR EXPT->-1-2))
     (43 14 (:LINEAR EXPT->-1-1))
     (43 14 (:LINEAR EXPT-<-1-2))
     (43 14 (:LINEAR EXPT-<-1-1))
     (33 31 (:REWRITE DEFAULT-*-1))
     (18 10 (:REWRITE ZIP-OPEN))
     (16 13 (:REWRITE DEFAULT-UNARY-MINUS))
     (6 2 (:REWRITE EQUAL-MINUS-0))
     (3 3 (:REWRITE ARITH-FOLD-CONSTS-IN-*))
     (2 2 (:REWRITE FOLD-CONSTS-IN-*))
     (2 2 (:REWRITE ARITH-INVERSE-OF-*-2)))
(ARITH-EXPT-NEGATIVE-CONSTANT-EXPONENT
     (6 6
        (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-2))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-1))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE)))
(ARITH-EXPONENTS-MULTIPLY
     (715 315 (:REWRITE DEFAULT-<-2))
     (524 52
          (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1))
     (524 52
          (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE<1))
     (524 52
          (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
     (524 52
          (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE<1))
     (395 315 (:REWRITE DEFAULT-<-1))
     (300 300
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (270 26 (:LINEAR EXPT->-1-2))
     (270 26 (:LINEAR EXPT->-1-1))
     (270 26 (:LINEAR EXPT-<-1-2))
     (270 26 (:LINEAR EXPT-<-1-1))
     (237 209
          (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (237 209
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
     (209 209
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-2))
     (209 209
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-1))
     (209 209
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
     (209 209
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (129 3 (:DEFINITION EXPT))
     (56 8 (:REWRITE DEFAULT-*-2))
     (18 6 (:REWRITE COMMUTATIVITY-OF-+))
     (12 12 (:REWRITE DEFAULT-+-2))
     (12 12 (:REWRITE DEFAULT-+-1))
     (12 3 (:REWRITE DEFAULT-UNARY-/))
     (11 8 (:REWRITE DEFAULT-*-1))
     (10 7 (:DEFINITION FIX))
     (9 3 (:REWRITE ZIP-OPEN))
     (6 2 (:REWRITE EQUAL-*-X-Y-0)))
(ARITH-DISTRIBUTIVITY-OF-EXPT-OVER-*
     (164 4 (:DEFINITION EXPT))
     (92 11 (:REWRITE DEFAULT-*-2))
     (53 53
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (53 53
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
     (53 53
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-2))
     (53 53
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-1))
     (53 53
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
     (53 53
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (32 11 (:REWRITE DEFAULT-*-1))
     (24 8 (:REWRITE COMMUTATIVITY-OF-+))
     (18 18
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (16 16 (:REWRITE DEFAULT-+-2))
     (16 16 (:REWRITE DEFAULT-+-1))
     (16 4 (:REWRITE DEFAULT-UNARY-/))
     (8 4 (:DEFINITION NOT))
     (8 4 (:DEFINITION FIX))
     (4 4 (:REWRITE ZIP-OPEN))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1)))
(ARITH-FIX-REVEALED (1 1
                       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(ARITH-RATIONAL-IMPLIES2 (1 1 (:REWRITE DEFAULT-UNARY-/))
                         (1 1 (:REWRITE DEFAULT-NUMERATOR))
                         (1 1 (:REWRITE DEFAULT-DENOMINATOR))
                         (1 1 (:REWRITE DEFAULT-*-2))
                         (1 1 (:REWRITE DEFAULT-*-1)))
(ARITH-EXPONENTS-ADD-1
     (344 8 (:DEFINITION EXPT))
     (180 20 (:REWRITE DEFAULT-*-2))
     (108 108
          (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (108 108
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
     (108 108
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-2))
     (108 108
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-1))
     (108 108
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
     (108 108
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (60 20 (:REWRITE DEFAULT-*-1))
     (48 16 (:REWRITE COMMUTATIVITY-OF-+))
     (40 40
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (37 37 (:REWRITE DEFAULT-+-2))
     (37 37 (:REWRITE DEFAULT-+-1))
     (32 8 (:REWRITE DEFAULT-UNARY-/))
     (16 8 (:DEFINITION FIX))
     (12 12 (:REWRITE DEFAULT-<-2))
     (12 12 (:REWRITE DEFAULT-<-1))
     (8 8 (:REWRITE ZIP-OPEN))
     (6 2
        (:REWRITE EXPONENTS-ADD-FOR-NONPOS-EXPONENTS))
     (6 2
        (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
     (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2 (:REWRITE EXPONENTS-ADD-2)))
(ARITH-EXPONENTS-ADD-FOR-NONPOS-EXPONENTSA
     (108 4 (:DEFINITION EXPT))
     (95 95
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (95 95
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
     (95 95
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-2))
     (95 95
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-1))
     (95 95
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
     (95 95
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (54 6 (:REWRITE DEFAULT-*-2))
     (22 6 (:REWRITE DEFAULT-*-1))
     (16 16
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (16 4 (:REWRITE DEFAULT-UNARY-/))
     (12 4 (:REWRITE COMMUTATIVITY-OF-+))
     (10 10 (:REWRITE DEFAULT-+-2))
     (10 10 (:REWRITE DEFAULT-+-1))
     (10 6 (:REWRITE ARITH-FIX-REVEALED))
     (8 4 (:DEFINITION FIX))
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (7 1 (:REWRITE ARITH-EXPONENTS-ADD-1))
     (4 4 (:REWRITE ZIP-OPEN))
     (4 1 (:REWRITE EQUAL-+-X-Y-0))
     (3 1
        (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
     (1 1 (:REWRITE EXPONENTS-ADD-2))
     (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(ARITH-EXPONENTS-ADD-FOR-NONNEG-EXPONENTSA
     (96 4 (:DEFINITION EXPT))
     (95 95
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (95 95
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
     (95 95
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-2))
     (95 95
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-1))
     (95 95
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
     (95 95
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (54 6 (:REWRITE DEFAULT-*-2))
     (26 6 (:REWRITE DEFAULT-*-1))
     (12 12
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (12 4 (:REWRITE COMMUTATIVITY-OF-+))
     (10 10 (:REWRITE DEFAULT-+-2))
     (10 10 (:REWRITE DEFAULT-+-1))
     (10 6 (:REWRITE ARITH-FIX-REVEALED))
     (8 4 (:DEFINITION FIX))
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (7 1 (:REWRITE ARITH-EXPONENTS-ADD-1))
     (4 4 (:REWRITE ZIP-OPEN))
     (4 1 (:REWRITE EQUAL-+-X-Y-0))
     (3 1
        (:REWRITE ARITH-EXPONENTS-ADD-FOR-NONPOS-EXPONENTSA))
     (1 1 (:REWRITE EXPONENTS-ADD-2))
     (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(ARITH-EXPONENTS-ADD-2
     (136 4 (:DEFINITION EXPT))
     (99 99
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (99 99
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP))
     (99 99
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-2))
     (99 99
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-1))
     (80 10 (:REWRITE DEFAULT-*-2))
     (24 10 (:REWRITE DEFAULT-*-1))
     (24 8 (:REWRITE COMMUTATIVITY-OF-+))
     (18 18 (:REWRITE DEFAULT-+-2))
     (18 18 (:REWRITE DEFAULT-+-1))
     (12 12
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (8 1 (:REWRITE ARITH-EXPONENTS-ADD-1))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (6 6 (:REWRITE ARITH-FIX-REVEALED))
     (5 1 (:REWRITE EQUAL-+-X-Y-0))
     (4 4 (:REWRITE ZIP-OPEN))
     (4 4 (:REWRITE DEFAULT-UNARY-/))
     (3 1
        (:REWRITE ARITH-EXPONENTS-ADD-FOR-NONPOS-EXPONENTSA))
     (3 1
        (:REWRITE ARITH-EXPONENTS-ADD-FOR-NONNEG-EXPONENTSA))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
