(RP::BIT-OF-BIT-OF-WHEN-0
 (3035 19 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2908 20 (:REWRITE |(* (* x y) z)|))
 (2634 10 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (2559 2559
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2559 2559
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2559 2559
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2559 2559
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (2480 270 (:REWRITE DEFAULT-TIMES-1))
 (2260 10 (:REWRITE FLOOR-ZERO . 3))
 (2250 270 (:REWRITE DEFAULT-TIMES-2))
 (2024 10 (:REWRITE CANCEL-FLOOR-+))
 (1684 20 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (1632 136 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (1632 136
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (1632 136
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (1632 136
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (1632 136
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (1468 10 (:REWRITE FLOOR-=-X/Y . 3))
 (1276 10 (:REWRITE FLOOR-=-X/Y . 2))
 (1266 56
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (964
  964
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (964 964
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (964
     964
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (964 964
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (964 964
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (884 136 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (884 136 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (884 136
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (884 136
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (884 136
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (884 136
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (884 136
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (884 136
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (884 136
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (884 136
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (760 10 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (676 16 (:REWRITE |(* (/ c) (expt d n))|))
 (676 10 (:REWRITE FLOOR-ZERO . 5))
 (676 10 (:REWRITE FLOOR-ZERO . 4))
 (620 60 (:REWRITE DEFAULT-DIVIDE))
 (570 19 (:REWRITE DEFAULT-FLOOR-1))
 (500 72
      (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
 (446 10 (:REWRITE |(integerp (- x))|))
 (414 22
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (414 22
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (398 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (384 34 (:REWRITE DEFAULT-PLUS-2))
 (370 52 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (364 54 (:REWRITE |(/ (expt x n))|))
 (360 146
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (306 306
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (306 306
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (306 306
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (288 10 (:REWRITE FLOOR-ZERO . 2))
 (288 10 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (288 10 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (284 4 (:REWRITE |(* (- (/ c)) (expt d n))|))
 (276 84 (:REWRITE DEFAULT-MINUS))
 (270 56 (:REWRITE DEFAULT-LESS-THAN-1))
 (216 56 (:REWRITE DEFAULT-LESS-THAN-2))
 (194 10 (:REWRITE FLOOR-CANCEL-*-CONST))
 (192 20 (:REWRITE |(* x (- y))|))
 (192 10 (:REWRITE |(* (- x) y)|))
 (188 188 (:TYPE-PRESCRIPTION RP::--))
 (160 52 (:REWRITE SIMPLIFY-SUMS-<))
 (149 19 (:REWRITE DEFAULT-FLOOR-2))
 (148 100 (:REWRITE DEFAULT-EXPT-2))
 (146 146
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (146 146
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (146 146
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (136 6 (:REWRITE |(* x (if a b c))|))
 (110 6
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (110 6
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (106 28
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (100 100 (:REWRITE DEFAULT-EXPT-1))
 (100 14 (:LINEAR EXPT->=-1-ONE))
 (96 96 (:REWRITE |(expt 1/c n)|))
 (96 96 (:REWRITE |(expt (- x) n)|))
 (96 4 (:REWRITE |(* x (expt x n))|))
 (90 6 (:REWRITE |(/ (if a b c))|))
 (68 56
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (68 56
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (64 4 (:REWRITE |(+ y x)|))
 (60 14 (:REWRITE ODD-EXPT-THM))
 (56 56 (:REWRITE THE-FLOOR-BELOW))
 (56 56 (:REWRITE THE-FLOOR-ABOVE))
 (56 56
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (56 56
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (56 56 (:REWRITE INTEGERP-<-CONSTANT))
 (56 56 (:REWRITE CONSTANT-<-INTEGERP))
 (56 56
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (56 56
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (56 56
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (56 56
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (56 56 (:REWRITE |(< c (- x))|))
 (56 56
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (56 56
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (56 56
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (56 56
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (56 56 (:REWRITE |(< (/ x) (/ y))|))
 (56 56 (:REWRITE |(< (- x) c)|))
 (56 56 (:REWRITE |(< (- x) (- y))|))
 (56 4 (:REWRITE |(* (/ x) (expt x n))|))
 (48 48 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (46 46 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (40 40 (:REWRITE REDUCE-INTEGERP-+))
 (40 40 (:REWRITE INTEGERP-MINUS-X))
 (40 40
     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (40 40 (:META META-INTEGERP-CORRECT))
 (36 32 (:REWRITE |(< (/ x) 0)|))
 (34 34 (:REWRITE DEFAULT-PLUS-1))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (32 32 (:REWRITE |(< (* x y) 0)|))
 (30 30
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 30 (:REWRITE NORMALIZE-ADDENDS))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (28 28
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (28 28
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (24 24 (:TYPE-PRESCRIPTION ABS))
 (22 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (22 22
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (22 22
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (22 22 (:REWRITE |(equal c (/ x))|))
 (22 22 (:REWRITE |(equal c (- x))|))
 (22 22 (:REWRITE |(equal (/ x) c)|))
 (22 22 (:REWRITE |(equal (/ x) (/ y))|))
 (22 22 (:REWRITE |(equal (- x) c)|))
 (22 22 (:REWRITE |(equal (- x) (- y))|))
 (22 14 (:LINEAR EXPT-X->=-X))
 (22 14 (:LINEAR EXPT-X->-X))
 (22 14 (:LINEAR EXPT->-1-ONE))
 (22 14 (:LINEAR EXPT-<=-1-TWO))
 (22 14 (:LINEAR EXPT-<-1-TWO))
 (20 20 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (20 20 (:REWRITE |(* c (* d x))|))
 (18 18
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<))
 (14 14 (:LINEAR EXPT->=-1-TWO))
 (14 14 (:LINEAR EXPT->-1-TWO))
 (14 14 (:LINEAR EXPT-<=-1-ONE))
 (14 14 (:LINEAR EXPT-<-1-ONE))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:REWRITE |(- (* c x))|))
 (6 6
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (6 6 (:REWRITE |(floor x (- y))| . 2))
 (6 6 (:REWRITE |(floor x (- y))| . 1))
 (6 6
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(floor (- x) y)| . 2))
 (6 6 (:REWRITE |(floor (- x) y)| . 1))
 (6 6
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:REWRITE UGLY-UNHIDE-HACK-THM-2))
 (2 2 (:REWRITE |(* 1/2 (floor x y))| . 3))
 (2 2 (:REWRITE |(* 1/2 (floor x y))| . 2)))
(RP::BINARY-XOR-OF-0
     (132 12
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (120 20 (:REWRITE ACL2-NUMBERP-X))
     (50 10 (:REWRITE RATIONALP-X))
     (38 8 (:REWRITE O-INFP->NEQ-0))
     (32 12
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (20 20
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (18 18 (:TYPE-PRESCRIPTION O-FINP))
     (18 6 (:REWRITE O-FIRST-EXPT-O-INFP))
     (12 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (12 12 (:REWRITE |(equal c (/ x))|))
     (12 12 (:REWRITE |(equal c (- x))|))
     (12 12 (:REWRITE |(equal (/ x) c)|))
     (12 12 (:REWRITE |(equal (/ x) (/ y))|))
     (12 12 (:REWRITE |(equal (- x) c)|))
     (12 12 (:REWRITE |(equal (- x) (- y))|))
     (12 6 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (10 10 (:REWRITE REDUCE-RATIONALP-+))
     (10 10 (:REWRITE REDUCE-RATIONALP-*))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE RATIONALP-MINUS-X))
     (10 10
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (10 10 (:META META-RATIONALP-CORRECT))
     (10 10 (:META META-INTEGERP-CORRECT))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::NOT$-OF-NOT$ (93 13 (:REWRITE ACL2-NUMBERP-X))
                  (47 9
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                  (40 8 (:REWRITE RATIONALP-X))
                  (23 21 (:REWRITE DEFAULT-PLUS-1))
                  (21 21 (:REWRITE DEFAULT-PLUS-2))
                  (16 3 (:REWRITE RP::+-IS-SUM))
                  (13 13
                      (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                  (12 2 (:REWRITE O-INFP->NEQ-0))
                  (11 11 (:REWRITE REDUCE-INTEGERP-+))
                  (11 11 (:REWRITE INTEGERP-MINUS-X))
                  (11 11
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                  (11 11 (:META META-INTEGERP-CORRECT))
                  (9 9
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (9 9
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (9 9
                     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (9 9 (:REWRITE |(equal c (/ x))|))
                  (9 9 (:REWRITE |(equal c (- x))|))
                  (9 9 (:REWRITE |(equal (/ x) c)|))
                  (9 9 (:REWRITE |(equal (/ x) (/ y))|))
                  (9 9 (:REWRITE |(equal (- x) c)|))
                  (9 9 (:REWRITE |(equal (- x) (- y))|))
                  (8 8 (:REWRITE REDUCE-RATIONALP-+))
                  (8 8 (:REWRITE REDUCE-RATIONALP-*))
                  (8 8 (:REWRITE RATIONALP-MINUS-X))
                  (8 8
                     (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                  (8 8 (:META META-RATIONALP-CORRECT))
                  (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (6 6 (:TYPE-PRESCRIPTION O-FINP))
                  (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
                  (5 1 (:REWRITE |(integerp (- x))|))
                  (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                  (3 3
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
                  (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                  (2 2
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BINARY-?-OF-CONSTANTS
     (593 17 (:REWRITE RP::BIT-FIX-OPENER))
     (563 11 (:DEFINITION BITP))
     (234 34 (:REWRITE ACL2-NUMBERP-X))
     (213 37
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (151 37
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (100 20 (:REWRITE RATIONALP-X))
     (60 38 (:REWRITE |(equal c (- x))|))
     (57 2
         (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (38 38
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (38 38
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (38 38 (:REWRITE |(equal c (/ x))|))
     (38 38 (:REWRITE |(equal (/ x) c)|))
     (38 38 (:REWRITE |(equal (/ x) (/ y))|))
     (38 38 (:REWRITE |(equal (- x) (- y))|))
     (37 37 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (37 37
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (37 37 (:REWRITE |(equal (- x) c)|))
     (34 34
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (20 20 (:REWRITE REDUCE-RATIONALP-+))
     (20 20 (:REWRITE REDUCE-RATIONALP-*))
     (20 20 (:REWRITE REDUCE-INTEGERP-+))
     (20 20 (:REWRITE RATIONALP-MINUS-X))
     (20 20
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (20 20 (:REWRITE INTEGERP-MINUS-X))
     (20 20
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (20 20 (:META META-RATIONALP-CORRECT))
     (20 20 (:META META-INTEGERP-CORRECT))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (11 11 (:TYPE-PRESCRIPTION BITP))
     (11 11 (:TYPE-PRESCRIPTION RP::BINARY-SUM))
     (8 4 (:REWRITE O-INFP->NEQ-0))
     (4 2 (:REWRITE DEFAULT-MINUS))
     (2 1 (:REWRITE DEFAULT-PLUS-2))
     (2 1 (:REWRITE |(- (- x))|))
     (1 1 (:REWRITE RP::SUM-COMM-1))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE DEFAULT-PLUS-1)))
(RP::AND$-OF-0 (56 1 (:REWRITE RP::BIT-FIX-OPENER))
               (54 1 (:DEFINITION BITP))
               (28 3
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (24 4 (:REWRITE ACL2-NUMBERP-X))
               (10 2 (:REWRITE RATIONALP-X))
               (8 3
                  (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (4 4
                  (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
               (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (3 3
                  (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
               (3 3
                  (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
               (3 3
                  (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
               (3 3 (:REWRITE |(equal c (/ x))|))
               (3 3 (:REWRITE |(equal c (- x))|))
               (3 3 (:REWRITE |(equal (/ x) c)|))
               (3 3 (:REWRITE |(equal (/ x) (/ y))|))
               (3 3 (:REWRITE |(equal (- x) c)|))
               (3 3 (:REWRITE |(equal (- x) (- y))|))
               (2 2 (:REWRITE REDUCE-RATIONALP-+))
               (2 2 (:REWRITE REDUCE-RATIONALP-*))
               (2 2 (:REWRITE REDUCE-INTEGERP-+))
               (2 2 (:REWRITE RATIONALP-MINUS-X))
               (2 2
                  (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
               (2 2 (:REWRITE INTEGERP-MINUS-X))
               (2 2
                  (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (2 2 (:META META-RATIONALP-CORRECT))
               (2 2 (:META META-INTEGERP-CORRECT))
               (1 1 (:TYPE-PRESCRIPTION BITP))
               (1 1
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::AND$-OF-1 (114 4 (:REWRITE RP::BIT-FIX-OPENER))
               (108 2 (:DEFINITION BITP))
               (60 8
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (48 8 (:REWRITE ACL2-NUMBERP-X))
               (20 8
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (20 4 (:REWRITE RATIONALP-X))
               (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (8 8
                  (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
               (8 8
                  (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
               (8 8
                  (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
               (8 8
                  (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
               (8 8 (:REWRITE |(equal c (/ x))|))
               (8 8 (:REWRITE |(equal c (- x))|))
               (8 8 (:REWRITE |(equal (/ x) c)|))
               (8 8 (:REWRITE |(equal (/ x) (/ y))|))
               (8 8 (:REWRITE |(equal (- x) c)|))
               (8 8 (:REWRITE |(equal (- x) (- y))|))
               (4 4
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
               (4 4 (:REWRITE REDUCE-RATIONALP-+))
               (4 4 (:REWRITE REDUCE-RATIONALP-*))
               (4 4 (:REWRITE REDUCE-INTEGERP-+))
               (4 4 (:REWRITE RATIONALP-MINUS-X))
               (4 4
                  (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
               (4 4 (:REWRITE INTEGERP-MINUS-X))
               (4 4
                  (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
               (4 4 (:META META-RATIONALP-CORRECT))
               (4 4 (:META META-INTEGERP-CORRECT))
               (4 2 (:REWRITE O-INFP->NEQ-0))
               (2 2 (:TYPE-PRESCRIPTION BITP)))
(RP::OR$-OF-0 (114 4 (:REWRITE RP::BIT-FIX-OPENER))
              (108 2 (:DEFINITION BITP))
              (56 6
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (48 8 (:REWRITE ACL2-NUMBERP-X))
              (20 4 (:REWRITE RATIONALP-X))
              (16 6
                  (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (8 8
                 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
              (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (6 6
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
              (6 6
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
              (6 6
                 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
              (6 6 (:REWRITE |(equal c (/ x))|))
              (6 6 (:REWRITE |(equal c (- x))|))
              (6 6 (:REWRITE |(equal (/ x) c)|))
              (6 6 (:REWRITE |(equal (/ x) (/ y))|))
              (6 6 (:REWRITE |(equal (- x) c)|))
              (6 6 (:REWRITE |(equal (- x) (- y))|))
              (4 4
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
              (4 4 (:REWRITE REDUCE-RATIONALP-+))
              (4 4 (:REWRITE REDUCE-RATIONALP-*))
              (4 4 (:REWRITE REDUCE-INTEGERP-+))
              (4 4 (:REWRITE RATIONALP-MINUS-X))
              (4 4
                 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
              (4 4 (:REWRITE INTEGERP-MINUS-X))
              (4 4
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (4 4 (:META META-RATIONALP-CORRECT))
              (4 4 (:META META-INTEGERP-CORRECT))
              (4 2 (:REWRITE O-INFP->NEQ-0))
              (2 2 (:TYPE-PRESCRIPTION BITP)))
(RP::OR$-OF-1 (56 1 (:REWRITE RP::BIT-FIX-OPENER))
              (54 1 (:DEFINITION BITP))
              (28 3
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (24 4 (:REWRITE ACL2-NUMBERP-X))
              (10 2 (:REWRITE RATIONALP-X))
              (8 3
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (4 4
                 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
              (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (3 3
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
              (3 3
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
              (3 3
                 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
              (3 3 (:REWRITE |(equal c (/ x))|))
              (3 3 (:REWRITE |(equal c (- x))|))
              (3 3 (:REWRITE |(equal (/ x) c)|))
              (3 3 (:REWRITE |(equal (/ x) (/ y))|))
              (3 3 (:REWRITE |(equal (- x) c)|))
              (3 3 (:REWRITE |(equal (- x) (- y))|))
              (2 2
                 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
              (2 2 (:REWRITE REDUCE-RATIONALP-+))
              (2 2 (:REWRITE REDUCE-RATIONALP-*))
              (2 2 (:REWRITE REDUCE-INTEGERP-+))
              (2 2 (:REWRITE RATIONALP-MINUS-X))
              (2 2
                 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
              (2 2 (:REWRITE INTEGERP-MINUS-X))
              (2 2
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (2 2 (:META META-RATIONALP-CORRECT))
              (2 2 (:META META-INTEGERP-CORRECT))
              (2 1 (:REWRITE O-INFP->NEQ-0))
              (1 1 (:TYPE-PRESCRIPTION BITP)))
(RP::EQUAL-OF-S-OF-C (26 2
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (24 4 (:REWRITE ACL2-NUMBERP-X))
                     (10 2 (:REWRITE RATIONALP-X))
                     (6 2
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (6 1 (:REWRITE O-INFP->NEQ-0))
                     (4 4
                        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                     (3 3 (:TYPE-PRESCRIPTION O-FINP))
                     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
                     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (2 2 (:REWRITE REDUCE-RATIONALP-+))
                     (2 2 (:REWRITE REDUCE-RATIONALP-*))
                     (2 2
                        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                     (2 2 (:REWRITE REDUCE-INTEGERP-+))
                     (2 2
                        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                     (2 2 (:REWRITE RATIONALP-MINUS-X))
                     (2 2
                        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                     (2 2 (:REWRITE INTEGERP-MINUS-X))
                     (2 2
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (2 2
                        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                     (2 2 (:REWRITE |(equal c (/ x))|))
                     (2 2 (:REWRITE |(equal c (- x))|))
                     (2 2 (:REWRITE |(equal (/ x) c)|))
                     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
                     (2 2 (:REWRITE |(equal (- x) c)|))
                     (2 2 (:REWRITE |(equal (- x) (- y))|))
                     (2 2 (:META META-RATIONALP-CORRECT))
                     (2 2 (:META META-INTEGERP-CORRECT))
                     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                     (1 1
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BINARY-APPEND-OPENER-CONS (6 6 (:TYPE-PRESCRIPTION BINARY-APPEND)))
(RP::BINARY-APPEND-OPENER-NIL (6 3
                                 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                              (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
                              (3 3 (:TYPE-PRESCRIPTION BINARY-APPEND)))
(RP::ASSOC-EQUAL-OPENER-CONS
     (65 15 (:REWRITE ACL2-NUMBERP-X))
     (65 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (25 5 (:REWRITE RATIONALP-X))
     (17 9 (:REWRITE DEFAULT-CAR))
     (15 15
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (15 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (15 5
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (8 2 (:REWRITE O-P-O-INFP-CAR))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (/ x))|))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (/ x) c)|))
     (5 5 (:REWRITE |(equal (/ x) (/ y))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:META META-RATIONALP-CORRECT))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 4 (:TYPE-PRESCRIPTION O-P))
     (3 3 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE O-P-DEF-O-FINP-1)))
(RP::ASSOC-EQUAL-OPENER-NIL
     (5 1
        (:REWRITE MEMBER-EQUAL-STRIP-CARS-ASSOC-EQUAL))
     (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1 1 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (1 1 (:DEFINITION MEMBER-EQUAL)))
(RP::M2-IS-BITP)
(RP::BINARY-XOR-1-OF-S
     (198 12
          (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (92 92 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (92 92 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (92 92 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (70 14 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (70 14 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (70 14
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (70 14
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (28 2 (:REWRITE DEFAULT-MOD-RATIO))
     (22 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (18 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (18 10
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (14 14 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (14 14
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (14 14 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (14 14
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (14 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (10 10 (:REWRITE |(equal c (/ x))|))
     (10 10 (:REWRITE |(equal c (- x))|))
     (10 10 (:REWRITE |(equal (/ x) c)|))
     (10 10 (:REWRITE |(equal (/ x) (/ y))|))
     (10 10 (:REWRITE |(equal (- x) c)|))
     (10 10 (:REWRITE |(equal (- x) (- y))|))
     (10 6 (:REWRITE DEFAULT-TIMES-2))
     (10 2 (:REWRITE |(* y x)|))
     (8 6 (:REWRITE DEFAULT-TIMES-1))
     (4 4
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 2 (:REWRITE DEFAULT-MOD-1))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:REWRITE DEFAULT-MOD-2))
     (2 2 (:REWRITE |(mod x 2)| . 2))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BINARY-NOT-OF-S (198 12
                          (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
                     (28 2 (:REWRITE DEFAULT-MOD-RATIO))
                     (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                     (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                     (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                     (21 9
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (19 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (17 9
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (10 6 (:REWRITE DEFAULT-TIMES-2))
                     (10 2 (:REWRITE |(* y x)|))
                     (9 9
                        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                     (9 9
                        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                     (9 9
                        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                     (9 9 (:REWRITE |(equal c (/ x))|))
                     (9 9 (:REWRITE |(equal c (- x))|))
                     (9 9 (:REWRITE |(equal (/ x) c)|))
                     (9 9 (:REWRITE |(equal (/ x) (/ y))|))
                     (9 9 (:REWRITE |(equal (- x) c)|))
                     (9 9 (:REWRITE |(equal (- x) (- y))|))
                     (8 6 (:REWRITE DEFAULT-TIMES-1))
                     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                     (4 4
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                     (4 2 (:REWRITE DEFAULT-MOD-1))
                     (2 2 (:REWRITE REDUCE-INTEGERP-+))
                     (2 2 (:REWRITE INTEGERP-MINUS-X))
                     (2 2
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (2 2 (:REWRITE DEFAULT-MOD-2))
                     (2 2 (:REWRITE |(mod x 2)| . 2))
                     (2 2 (:META META-INTEGERP-CORRECT)))
(RP::BINARY-NOT-OF-C
     (1406 98
           (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (316 10
          (:REWRITE RP::DUMMY-SUM-CANCEL-LEMMA1))
     (161 62
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (158 62 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (132 62
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (116 5 (:REWRITE RP::F2-OF-BIT))
     (62 62
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (62 62
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (62 62
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (62 62 (:REWRITE |(equal c (/ x))|))
     (62 62 (:REWRITE |(equal c (- x))|))
     (62 62 (:REWRITE |(equal (/ x) c)|))
     (62 62 (:REWRITE |(equal (/ x) (/ y))|))
     (62 62 (:REWRITE |(equal (- x) c)|))
     (62 62 (:REWRITE |(equal (- x) (- y))|))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 1 (:REWRITE O-INFP->NEQ-0)))
(RP::BINARY-NOT-OF-S-C-RES
     (3 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BINARY-NOT-OF-S-SIDE-COND
     (418 16
          (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (44 17
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (41 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (32 17
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (32 3 (:REWRITE DEFAULT-MOD-RATIO))
     (17 17
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (17 17
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (17 17
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (17 17 (:REWRITE |(equal c (/ x))|))
     (17 17 (:REWRITE |(equal c (- x))|))
     (17 17 (:REWRITE |(equal (/ x) c)|))
     (17 17 (:REWRITE |(equal (/ x) (/ y))|))
     (17 17 (:REWRITE |(equal (- x) c)|))
     (17 17 (:REWRITE |(equal (- x) (- y))|))
     (15 9 (:REWRITE DEFAULT-TIMES-2))
     (15 3 (:REWRITE |(* y x)|))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (12 9 (:REWRITE DEFAULT-TIMES-1))
     (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (7 7 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6 3 (:REWRITE DEFAULT-MOD-1))
     (3 3 (:REWRITE DEFAULT-MOD-2))
     (3 3 (:REWRITE |(mod x 2)| . 2))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RP::BINARY-NOT-OF-C-SIDE-COND
     (1832 88
           (:REWRITE RP::SUM-OF-NEGATED-ELEMENTS))
     (416 8
          (:REWRITE RP::DUMMY-SUM-CANCEL-LEMMA1))
     (214 82
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (210 82 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (175 82
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (152 4 (:REWRITE RP::F2-OF-BIT))
     (82 82
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (82 82
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (82 82
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (82 82 (:REWRITE |(equal c (/ x))|))
     (82 82 (:REWRITE |(equal c (- x))|))
     (82 82 (:REWRITE |(equal (/ x) c)|))
     (82 82 (:REWRITE |(equal (/ x) (/ y))|))
     (82 82 (:REWRITE |(equal (- x) c)|))
     (82 82 (:REWRITE |(equal (- x) (- y))|))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 1 (:REWRITE O-INFP->NEQ-0)))
(RP::BINARY-NOT-OF-S-C-RES-SIDE-COND
     (3 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::BINARY-NOT-OF-BINARY-SUM
     (15 15 (:REWRITE DEFAULT-PLUS-2))
     (15 15 (:REWRITE DEFAULT-PLUS-1))
     (12 12 (:REWRITE DEFAULT-MINUS))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE NORMALIZE-ADDENDS))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (8 8
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (8 8 (:REWRITE |(equal c (/ x))|))
     (8 8 (:REWRITE |(equal (/ x) c)|))
     (8 8 (:REWRITE |(equal (/ x) (/ y))|))
     (8 8 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 6
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3 (:REWRITE O-INFP->NEQ-0))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE |(+ c (+ d x))|)))
(RP::BINARY-NOT-OF-BINARY-SUM-SIDE-COND
     (18 18 (:REWRITE DEFAULT-MINUS))
     (16 16 (:REWRITE DEFAULT-PLUS-2))
     (16 16 (:REWRITE DEFAULT-PLUS-1))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE NORMALIZE-ADDENDS))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (9 9
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (9 9 (:REWRITE |(equal c (/ x))|))
     (9 9 (:REWRITE |(equal c (- x))|))
     (9 9 (:REWRITE |(equal (/ x) c)|))
     (9 9 (:REWRITE |(equal (/ x) (/ y))|))
     (9 9 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 6
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3 (:REWRITE O-INFP->NEQ-0))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE |(+ c (+ d x))|)))
(RP::--OF--- (4 2 (:REWRITE DEFAULT-MINUS))
             (1 1 (:REWRITE REDUCE-INTEGERP-+))
             (1 1 (:REWRITE INTEGERP-MINUS-X))
             (1 1
                (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
             (1 1 (:META META-INTEGERP-CORRECT)))
(RP::--OF-SUM (11 5 (:REWRITE DEFAULT-MINUS))
              (6 3 (:REWRITE DEFAULT-PLUS-2))
              (6 3 (:REWRITE DEFAULT-PLUS-1))
              (3 3
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (3 3 (:REWRITE NORMALIZE-ADDENDS))
              (2 2 (:REWRITE REDUCE-INTEGERP-+))
              (2 2 (:REWRITE INTEGERP-MINUS-X))
              (2 2
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (2 2 (:META META-INTEGERP-CORRECT)))
(RP::EQUAL-SIDES-TO-S
     (78 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (72 12 (:REWRITE ACL2-NUMBERP-X))
     (30 6 (:REWRITE RATIONALP-X))
     (18 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 3 (:REWRITE O-INFP->NEQ-0))
     (12 12
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (9 9 (:TYPE-PRESCRIPTION O-FINP))
     (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:META META-RATIONALP-CORRECT))
     (6 6 (:META META-INTEGERP-CORRECT))
     (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::S-C-SPEC-WITH-ZERO)
(RP::S-C-SPEC-WITH-ONE
     (26 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (24 4 (:REWRITE ACL2-NUMBERP-X))
     (10 2 (:REWRITE RATIONALP-X))
     (8 2 (:REWRITE RP::EQUAL-SIDES-TO-S))
     (6 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (4 4
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(RP::PLUS-WITH-0 (3 3 (:REWRITE DEFAULT-PLUS-2))
                 (3 3 (:REWRITE DEFAULT-PLUS-1))
                 (1 1 (:REWRITE REDUCE-INTEGERP-+))
                 (1 1 (:REWRITE INTEGERP-MINUS-X))
                 (1 1
                    (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                 (1 1 (:META META-INTEGERP-CORRECT)))
