(UBYTE128P-OF-LOGHEAD-OF-128
     (111 111
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (111 111
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (111 111
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (100 20 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (100 20 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (100 20
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (100 20
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (66 1 (:REWRITE CANCEL-MOD-+))
     (44 1 (:REWRITE MOD-X-Y-=-X . 4))
     (44 1 (:REWRITE MOD-X-Y-=-X . 3))
     (42 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (39 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (32 4 (:REWRITE INTEGERP-MINUS-X))
     (27 1 (:REWRITE MOD-ZERO . 4))
     (27 1 (:REWRITE MOD-ZERO . 3))
     (27 1 (:LINEAR MOD-BOUNDS-3))
     (22 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (21 2 (:REWRITE |(* (- x) y)|))
     (20 20 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (20 20
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (20 20 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (20 20
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (20 20 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (20 4 (:REWRITE |(* y x)|))
     (17 11 (:REWRITE DEFAULT-TIMES-2))
     (16 11 (:REWRITE DEFAULT-TIMES-1))
     (14 1 (:REWRITE DEFAULT-MOD-RATIO))
     (12 2 (:REWRITE DEFAULT-MINUS))
     (12 2 (:LINEAR MOD-BOUNDS-2))
     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (11 2 (:REWRITE |(- (* c x))|))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 1 (:REWRITE MOD-X-Y-=-X . 2))
     (7 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (7 1
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (6 6
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (6 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (6 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (6 1
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (6 1 (:REWRITE MOD-CANCEL-*-CONST))
     (6 1
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (5 4 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
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
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE DEFAULT-MOD-1))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-MOD-2))
     (1 1 (:REWRITE |(mod x (- y))| . 3))
     (1 1 (:REWRITE |(mod x (- y))| . 2))
     (1 1 (:REWRITE |(mod x (- y))| . 1))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(mod (- x) y)| . 3))
     (1 1 (:REWRITE |(mod (- x) y)| . 2))
     (1 1 (:REWRITE |(mod (- x) y)| . 1))
     (1 1
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
