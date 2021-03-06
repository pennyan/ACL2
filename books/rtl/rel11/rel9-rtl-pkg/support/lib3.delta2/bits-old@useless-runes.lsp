(RTL::NATS)
(RTL::BVECP-MEMBER-1
     (33 9 (:REWRITE ACL2-NUMBERP-X))
     (31 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (29 27 (:REWRITE DEFAULT-PLUS-1))
     (27 27 (:REWRITE DEFAULT-PLUS-2))
     (17 17 (:REWRITE THE-FLOOR-BELOW))
     (17 17 (:REWRITE THE-FLOOR-ABOVE))
     (17 17
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (17 17
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (17 17 (:REWRITE DEFAULT-LESS-THAN-2))
     (17 17 (:REWRITE DEFAULT-LESS-THAN-1))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (13 13
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (13 13 (:REWRITE INTEGERP-<-CONSTANT))
     (13 13 (:REWRITE CONSTANT-<-INTEGERP))
     (13 13
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (13 13
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (13 13
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (13 13
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (13 13 (:REWRITE |(< c (- x))|))
     (13 13
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (13 13
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (13 13
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (13 13
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (13 13 (:REWRITE |(< (/ x) (/ y))|))
     (13 13 (:REWRITE |(< (- x) c)|))
     (13 13 (:REWRITE |(< (- x) (- y))|))
     (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 3 (:REWRITE RATIONALP-X))
     (9 9 (:REWRITE REDUCE-INTEGERP-+))
     (9 9 (:REWRITE INTEGERP-MINUS-X))
     (9 9 (:META META-INTEGERP-CORRECT))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 5 (:REWRITE DEFAULT-CAR))
     (7 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (7 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 4 (:REWRITE DEFAULT-CDR))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE DEFAULT-TIMES-2))
     (4 4 (:REWRITE DEFAULT-TIMES-1))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3 (:REWRITE |(< (+ c/d x) y)|))
     (3 3 (:META META-RATIONALP-CORRECT))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::BVECP-MEMBER
 (45
   45
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (45
  45
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (45 45
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (31 1 (:LINEAR EXPT-<=-1-TWO))
 (30 1 (:LINEAR EXPT->-1-ONE))
 (26 1 (:LINEAR EXPT-X->=-X))
 (26 1 (:LINEAR EXPT-X->-X))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-1))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< c (- x))|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::BITS-BITS-SUM-NEW
     (298 20
          (:REWRITE RTL::BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
     (252 20 (:REWRITE RTL::BITS-NEG))
     (239 14 (:REWRITE RTL::BITS-TAIL-2))
     (217 7 (:DEFINITION NATP))
     (93 79 (:REWRITE DEFAULT-PLUS-1))
     (85 79 (:REWRITE DEFAULT-PLUS-2))
     (80 14 (:REWRITE RTL::BITS-TAIL))
     (79 31
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (35 7 (:REWRITE |(equal (/ x) c)|))
     (34 34 (:REWRITE THE-FLOOR-BELOW))
     (34 34 (:REWRITE THE-FLOOR-ABOVE))
     (34 34
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (34 34
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (34 34
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (34 34
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (34 34 (:REWRITE INTEGERP-<-CONSTANT))
     (34 34 (:REWRITE DEFAULT-LESS-THAN-2))
     (34 34 (:REWRITE DEFAULT-LESS-THAN-1))
     (34 34 (:REWRITE CONSTANT-<-INTEGERP))
     (34 34
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (34 34
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (34 34
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (34 34
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (34 34 (:REWRITE |(< c (- x))|))
     (34 34
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (34 34
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (34 34
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (34 34
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (34 34 (:REWRITE |(< (/ x) (/ y))|))
     (34 34 (:REWRITE |(< (- x) c)|))
     (34 34 (:REWRITE |(< (- x) (- y))|))
     (31 31 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (25 25 (:REWRITE |(< (/ x) 0)|))
     (25 25 (:REWRITE |(< (* x y) 0)|))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (21 21
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (11 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (11 5
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (7 7 (:TYPE-PRESCRIPTION NATP))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (7 7 (:REWRITE |(equal c (/ x))|))
     (7 7 (:REWRITE |(equal (/ x) (/ y))|))
     (7 7 (:REWRITE |(equal (- x) (- y))|))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (5 5 (:REWRITE |(equal c (- x))|))
     (5 5 (:REWRITE |(equal (- x) c)|))
     (5 5 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE DEFAULT-DIVIDE))
     (2 2 (:REWRITE |(not (equal x (/ y)))|))
     (2 2 (:REWRITE |(equal x (/ y))|))
     (2 2 (:REWRITE |(/ (/ x))|)))
(RTL::BITS-BITS-SUM-ALT
     (241 17
          (:REWRITE RTL::BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
     (206 13 (:REWRITE RTL::BITS-TAIL-2))
     (191 17 (:REWRITE RTL::BITS-NEG))
     (186 6 (:DEFINITION NATP))
     (89 76 (:REWRITE DEFAULT-PLUS-1))
     (81 76 (:REWRITE DEFAULT-PLUS-2))
     (73 13 (:REWRITE RTL::BITS-TAIL))
     (72 24
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (34 6 (:REWRITE |(equal (/ x) c)|))
     (27 27 (:REWRITE THE-FLOOR-BELOW))
     (27 27 (:REWRITE THE-FLOOR-ABOVE))
     (27 27
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (27 27
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (27 27
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (27 27
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (27 27 (:REWRITE INTEGERP-<-CONSTANT))
     (27 27 (:REWRITE DEFAULT-LESS-THAN-2))
     (27 27 (:REWRITE DEFAULT-LESS-THAN-1))
     (27 27 (:REWRITE CONSTANT-<-INTEGERP))
     (27 27
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (27 27
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (27 27
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (27 27
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (27 27 (:REWRITE |(< c (- x))|))
     (27 27
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (27 27
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (27 27
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (27 27
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (27 27 (:REWRITE |(< (/ x) (/ y))|))
     (27 27 (:REWRITE |(< (- x) c)|))
     (27 27 (:REWRITE |(< (- x) (- y))|))
     (24 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (20 20 (:REWRITE |(< (/ x) 0)|))
     (20 20 (:REWRITE |(< (* x y) 0)|))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6 (:TYPE-PRESCRIPTION NATP))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE DEFAULT-DIVIDE))
     (2 2 (:REWRITE |(not (equal x (/ y)))|))
     (2 2 (:REWRITE |(equal x (/ y))|))
     (2 2 (:REWRITE |(/ (/ x))|)))
(RTL::BITS-BITS-DIFF-NEW
     (156 11 (:REWRITE RTL::BITS-NEG))
     (108 12 (:REWRITE RTL::BITS-TAIL-2))
     (72 12 (:REWRITE RTL::BITS-TAIL))
     (52 49 (:REWRITE DEFAULT-PLUS-2))
     (49 49 (:REWRITE DEFAULT-PLUS-1))
     (24 24 (:REWRITE THE-FLOOR-BELOW))
     (24 24 (:REWRITE THE-FLOOR-ABOVE))
     (24 24
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (24 24
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (24 24
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (24 24
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (24 24 (:REWRITE INTEGERP-<-CONSTANT))
     (24 24 (:REWRITE DEFAULT-LESS-THAN-2))
     (24 24 (:REWRITE DEFAULT-LESS-THAN-1))
     (24 24 (:REWRITE CONSTANT-<-INTEGERP))
     (24 24
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (24 24
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (24 24
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (24 24
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (24 24 (:REWRITE |(< c (- x))|))
     (24 24
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (24 24
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (24 24
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (24 24
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (24 24 (:REWRITE |(< (/ x) (/ y))|))
     (24 24 (:REWRITE |(< (- x) c)|))
     (24 24 (:REWRITE |(< (- x) (- y))|))
     (19 19
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (19 19 (:REWRITE NORMALIZE-ADDENDS))
     (17 17 (:REWRITE |(< (/ x) 0)|))
     (17 17 (:REWRITE |(< (* x y) 0)|))
     (16 16 (:REWRITE SIMPLIFY-SUMS-<))
     (16 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (16 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (12 9 (:REWRITE DEFAULT-MINUS))
     (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:META META-INTEGERP-CORRECT))
     (3 3 (:TYPE-PRESCRIPTION NATP))
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
     (2 2 (:REWRITE |(equal (- x) (- y))|)))
(RTL::BITS-BITS-PROD
     (156 11 (:REWRITE RTL::BITS-NEG))
     (148 11
          (:REWRITE RTL::BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
     (103 7 (:REWRITE RTL::BITS-TAIL-2))
     (93 3 (:DEFINITION NATP))
     (43 7 (:REWRITE RTL::BITS-TAIL))
     (18 18 (:REWRITE DEFAULT-PLUS-2))
     (18 18 (:REWRITE DEFAULT-PLUS-1))
     (17 17 (:REWRITE THE-FLOOR-BELOW))
     (17 17 (:REWRITE THE-FLOOR-ABOVE))
     (17 17
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (17 17
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (17 17
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (17 17
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (17 17 (:REWRITE INTEGERP-<-CONSTANT))
     (17 17 (:REWRITE DEFAULT-LESS-THAN-2))
     (17 17 (:REWRITE DEFAULT-LESS-THAN-1))
     (17 17 (:REWRITE CONSTANT-<-INTEGERP))
     (17 17
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (17 17
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (17 17
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (17 17
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (17 17 (:REWRITE |(< c (- x))|))
     (17 17
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (17 17
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (17 17
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (17 17
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (17 17 (:REWRITE |(< (/ x) (/ y))|))
     (17 17 (:REWRITE |(< (- x) c)|))
     (17 17 (:REWRITE |(< (- x) (- y))|))
     (13 13 (:REWRITE SIMPLIFY-SUMS-<))
     (13 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (13 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (13 13 (:REWRITE |(< (/ x) 0)|))
     (13 13 (:REWRITE |(< (* x y) 0)|))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (11 8 (:REWRITE DEFAULT-TIMES-2))
     (9 8 (:REWRITE DEFAULT-TIMES-1))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3 (:TYPE-PRESCRIPTION NATP))
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
     (2 2 (:REWRITE |(equal (- x) (- y))|)))
(RTL::BITS-FL-DIFF)
(RTL::BITS-NEG-INDICES)
(RTL::BITS-REVERSE-INDICES)
(RTL::NEG-BITS-1-NEW
 (414 22
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (245 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (181 3 (:LINEAR EXPT-<=-1-TWO))
 (154 3 (:LINEAR EXPT-X->=-X))
 (154 3 (:LINEAR EXPT-X->-X))
 (119 3 (:LINEAR EXPT-<-1-TWO))
 (116 8 (:REWRITE |(+ y (+ x z))|))
 (89
  89
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (89 89
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (89 89
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (89 89
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (89 89
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (50 46 (:REWRITE DEFAULT-PLUS-1))
 (46 46 (:REWRITE DEFAULT-PLUS-2))
 (36 12 (:REWRITE NORMALIZE-ADDENDS))
 (36 5 (:REWRITE |(< y (+ (- c) x))|))
 (35 3 (:REWRITE |(< (+ (- c) x) y)|))
 (34 8 (:REWRITE |(+ y x)|))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 22
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (22 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (22 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (22 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (20 8 (:REWRITE |(+ c (+ d x))|))
 (16 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE CONSTANT-<-INTEGERP))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< c (- x))|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (12 12 (:REWRITE SIMPLIFY-SUMS-<))
 (11 11 (:REWRITE DEFAULT-EXPT-2))
 (11 11 (:REWRITE DEFAULT-EXPT-1))
 (11 11 (:REWRITE |(expt 1/c n)|))
 (11 11 (:REWRITE |(expt (- x) n)|))
 (10 10 (:REWRITE |(+ 0 x)|))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:DEFINITION FIX))
 (8 4 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(+ x (- x))|))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::BITS-MINUS-1-NEW
 (812 28
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (474 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (238 2 (:LINEAR EXPT-<=-1-TWO))
 (234 2 (:LINEAR EXPT-<-1-TWO))
 (232 16 (:REWRITE |(+ y (+ x z))|))
 (204 2 (:LINEAR EXPT-X->=-X))
 (204 2 (:LINEAR EXPT-X->-X))
 (100 92 (:REWRITE DEFAULT-PLUS-1))
 (92 92 (:REWRITE DEFAULT-PLUS-2))
 (72 24 (:REWRITE NORMALIZE-ADDENDS))
 (72 10 (:REWRITE |(< y (+ (- c) x))|))
 (70 6 (:REWRITE |(< (+ (- c) x) y)|))
 (68 16 (:REWRITE |(+ y x)|))
 (40 16 (:REWRITE |(+ c (+ d x))|))
 (37
  37
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (28 28 (:REWRITE THE-FLOOR-BELOW))
 (28 28 (:REWRITE THE-FLOOR-ABOVE))
 (28 28
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (28 28
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (28 28 (:REWRITE DEFAULT-LESS-THAN-2))
 (28 28 (:REWRITE DEFAULT-LESS-THAN-1))
 (20 20 (:REWRITE |(+ 0 x)|))
 (16 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE CONSTANT-<-INTEGERP))
 (16 16 (:REWRITE |(< x (+ c/d y))|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< c (- x))|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (16 16 (:DEFINITION FIX))
 (16 8 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE |(< (+ c/d x) y)|))
 (8 8 (:REWRITE |(+ x (- x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE DEFAULT-EXPT-2))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(RTL::BITS-DIFF-0
 (713 59
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (272
  272
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (272 272
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (272
     272
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (272 272
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (272 272
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (272 272
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (245 5 (:REWRITE ODD-EXPT-THM))
 (208 42 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (123 60 (:REWRITE DEFAULT-LESS-THAN-2))
 (108 98 (:REWRITE DEFAULT-PLUS-2))
 (105 42
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (102 2 (:LINEAR EXPT-X->=-X))
 (102 2 (:LINEAR EXPT-X->-X))
 (101 98 (:REWRITE DEFAULT-PLUS-1))
 (98 2 (:LINEAR EXPT->=-1-ONE))
 (98 2 (:LINEAR EXPT-<=-1-TWO))
 (96 42
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (96 2 (:LINEAR EXPT->-1-ONE))
 (96 2 (:LINEAR EXPT-<-1-TWO))
 (90 3 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (90 3 (:REWRITE RTL::BITS-NEG-INDICES))
 (86 41 (:REWRITE SIMPLIFY-SUMS-<))
 (68 17 (:REWRITE |(+ c (+ d x))|))
 (67 3 (:REWRITE RTL::BITS-TAIL-2))
 (62 2 (:DEFINITION NATP))
 (60 60 (:REWRITE THE-FLOOR-BELOW))
 (60 60 (:REWRITE THE-FLOOR-ABOVE))
 (60 60 (:REWRITE DEFAULT-LESS-THAN-1))
 (59 59
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (59 59
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (42 42 (:REWRITE INTEGERP-<-CONSTANT))
 (42 42 (:REWRITE CONSTANT-<-INTEGERP))
 (42 42
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (42 42
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (42 42
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (42 42
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (42 42 (:REWRITE |(< c (- x))|))
 (42 42
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (42 42
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (42 42
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (42 42
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (42 42 (:REWRITE |(< (/ x) (/ y))|))
 (42 42 (:REWRITE |(< (- x) c)|))
 (42 42 (:REWRITE |(< (- x) (- y))|))
 (30 30
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 1
     (:REWRITE RTL::BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (30 1 (:REWRITE RTL::BITS-NEG))
 (24 24 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (19 19 (:REWRITE |(< (* x y) 0)|))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (14 14 (:REWRITE |(< x (+ c/d y))|))
 (14 14 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:META META-INTEGERP-CORRECT))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (6 1 (:REWRITE ACL2-NUMBERP-X))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3 3 (:REWRITE DEFAULT-MINUS))
 (2 2 (:TYPE-PRESCRIPTION NATP))
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
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-X))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::BITS-TAIL-GEN
 (154
  154
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (154 154
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (154
     154
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (154 154
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (154 154
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (96 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (77 2 (:LINEAR EXPT-X->=-X))
 (77 2 (:LINEAR EXPT-X->-X))
 (32 14 (:REWRITE DEFAULT-LESS-THAN-2))
 (32 2 (:LINEAR EXPT-<=-1-TWO))
 (31 13 (:REWRITE DEFAULT-PLUS-2))
 (31 1 (:REWRITE ODD-EXPT-THM))
 (30 12 (:REWRITE SIMPLIFY-SUMS-<))
 (30 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (30 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (30 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (25 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (22 2 (:REWRITE |(+ y (+ x z))|))
 (14 14 (:REWRITE THE-FLOOR-BELOW))
 (14 14 (:REWRITE THE-FLOOR-ABOVE))
 (14 14
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (14 14 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 13 (:REWRITE DEFAULT-PLUS-1))
 (12 12 (:REWRITE INTEGERP-<-CONSTANT))
 (12 12 (:REWRITE CONSTANT-<-INTEGERP))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< c (- x))|))
 (12 12
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (12 12
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (12 12
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (12 12 (:REWRITE |(< (/ x) (/ y))|))
 (12 12 (:REWRITE |(< (- x) c)|))
 (12 12 (:REWRITE |(< (- x) (- y))|))
 (10 1 (:REWRITE DEFAULT-MINUS))
 (9 9 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (8 2 (:REWRITE |(+ c (+ d x))|))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(+ 0 x)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::BITS-SHIFT-UP-1-NEW)
(RTL::BITS-SHIFT-UP-2-NEW)
(RTL::BITN-MINUS-1-NEW
 (6
  6
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6 6
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::BITN-SHIFT-UP)
(RTL::BITN-PLUS-BITS-NEW)
(RTL::DIFF-BIT)
(RTL::DIFF-BIT-REWRITE
     (80 20 (:REWRITE RTL::NEG-BITN-2))
     (80 20 (:REWRITE RTL::NEG-BITN-1))
     (80 20 (:REWRITE RTL::NEG-BITN-0))
     (60 60 (:REWRITE REDUCE-INTEGERP-+))
     (60 60 (:REWRITE INTEGERP-MINUS-X))
     (60 60 (:META META-INTEGERP-CORRECT))
     (60 20 (:REWRITE RTL::BVECP-BITN-0))
     (30 30
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (30 30 (:REWRITE NORMALIZE-ADDENDS))
     (30 30 (:REWRITE DEFAULT-PLUS-2))
     (30 30 (:REWRITE DEFAULT-PLUS-1))
     (27 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (27 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (27 9
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (20 20 (:REWRITE RTL::BITN-NEG))
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
     (7 7 (:REWRITE ZP-OPEN)))
(RTL::DIFF-BIT-BOUNDS
     (142 2 (:DEFINITION RTL::SUMBITS-BADGUY))
     (20 20
         (:TYPE-PRESCRIPTION RTL::BITN-NONNEGATIVE-INTEGER))
     (16 4 (:REWRITE RTL::NEG-BITN-2))
     (16 4 (:REWRITE RTL::NEG-BITN-1))
     (16 4 (:REWRITE RTL::NEG-BITN-0))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (13 13 (:META META-INTEGERP-CORRECT))
     (12 4 (:REWRITE RTL::BVECP-BITN-0))
     (8 8 (:TYPE-PRESCRIPTION RTL::BVECP))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
     (8 8 (:REWRITE DEFAULT-PLUS-2))
     (8 8 (:REWRITE DEFAULT-PLUS-1))
     (8 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 5 (:REWRITE SIMPLIFY-SUMS-<))
     (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< c (- x))|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE RTL::BITN-NEG))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
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
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::DIFF-BIT-EQUAL
 (68
   68
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (68
  68
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (26 1 (:LINEAR EXPT-X->=-X))
 (26 1 (:LINEAR EXPT-X->-X))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (- x))|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) (/ y))|))
 (2 2 (:REWRITE |(< (- x) c)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::BITS-BITS-SUM)
(RTL::BITS-BITS-DIFF)
(RTL::NEG-BITS-1)
(RTL::BITS-MINUS-1)
(RTL::BITS-SHIFT-UP-1)
(RTL::BITS-SHIFT-UP-2)
(RTL::BITN-MINUS-1
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::BITN-PLUS-BITS)
(RTL::INTVAL
 (5
   5
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (5
  5
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::INTVAL-REWRITE
 (92 2 (:REWRITE RTL::BITN-NEG))
 (82 2 (:REWRITE |(< (if a b c) x)|))
 (72 8 (:REWRITE ACL2-NUMBERP-X))
 (64 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (40 4 (:REWRITE DEFAULT-MINUS))
 (32 8 (:REWRITE RATIONALP-X))
 (18 18 (:REWRITE REDUCE-INTEGERP-+))
 (18 18 (:REWRITE INTEGERP-MINUS-X))
 (18 18 (:META META-INTEGERP-CORRECT))
 (12
   12
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (12
  12
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (11 11 (:TYPE-PRESCRIPTION RTL::SGNDINTVAL))
 (11 11 (:TYPE-PRESCRIPTION RTL::INTVAL))
 (8 8 (:REWRITE REDUCE-RATIONALP-+))
 (8 8 (:REWRITE REDUCE-RATIONALP-*))
 (8 8 (:REWRITE RATIONALP-MINUS-X))
 (8 8 (:META META-RATIONALP-CORRECT))
 (8 2 (:REWRITE RTL::NEG-BITN-2))
 (8 2 (:REWRITE RTL::NEG-BITN-1))
 (8 2 (:REWRITE RTL::NEG-BITN-0))
 (8 2 (:REWRITE |(+ c (+ d x))|))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:REWRITE NORMALIZE-ADDENDS))
 (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (6 2 (:REWRITE RTL::BVECP-BITN-0))
 (4 4 (:TYPE-PRESCRIPTION RTL::BVECP))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (- x))|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) (/ y))|))
 (2 2 (:REWRITE |(< (- x) c)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(+ 0 x)|)))
(RTL::INTVAL-BITS
 (194 12
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (93
  93
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (93 93
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (93 93
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (93 93
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (93 93
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (93 93
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (42 1 (:LINEAR EXPT->=-1-ONE))
 (42 1 (:LINEAR EXPT-<=-1-TWO))
 (41 1 (:LINEAR EXPT->-1-ONE))
 (41 1 (:LINEAR EXPT-<-1-TWO))
 (40 1 (:LINEAR EXPT-X->=-X))
 (40 1 (:LINEAR EXPT-X->-X))
 (24 6 (:REWRITE |(+ c (+ d x))|))
 (12 12 (:REWRITE THE-FLOOR-BELOW))
 (12 12 (:REWRITE THE-FLOOR-ABOVE))
 (12 12
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12 (:REWRITE DEFAULT-PLUS-2))
 (12 12 (:REWRITE DEFAULT-PLUS-1))
 (12 12 (:REWRITE DEFAULT-LESS-THAN-2))
 (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:REWRITE |(+ 0 x)|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(RTL::SIGN-EXTEND (3 3 (:TYPE-PRESCRIPTION RTL::INTVAL)))
(RTL::SIGN-EXTEND-REWRITE)
(RTL::INTVAL-SIGN-EXTEND
 (62 2 (:LINEAR EXPT-<=-1-TWO))
 (60 2 (:LINEAR EXPT->-1-ONE))
 (52 2 (:LINEAR EXPT-X->=-X))
 (52 2 (:LINEAR EXPT-X->-X))
 (40
   40
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (40
  40
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (9 9 (:REWRITE DEFAULT-EXPT-2))
 (9 9 (:REWRITE DEFAULT-EXPT-1))
 (9 9 (:REWRITE |(expt 1/c n)|))
 (9 9 (:REWRITE |(expt (- x) n)|))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (8 8 (:REWRITE CONSTANT-<-INTEGERP))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< c (- x))|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< (/ x) (/ y))|))
 (8 8 (:REWRITE |(< (- x) c)|))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
