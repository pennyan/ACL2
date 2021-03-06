(STR::__CAT-LIST)
(STR::__PAD-NUMBER-TRIPLE (1 1
                             (:TYPE-PRESCRIPTION STR::__PAD-NUMBER-TRIPLE)))
(STR::LEMMA
     (57930 6930 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (34050 6930 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (34050 6930
            (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (32222 1202 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (32222 1202
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (32222 1202
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (15574 206 (:REWRITE MOD-X-Y-=-X . 3))
     (14580 13900
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (13900 13900
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (13900 13900
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (13900 13900
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11370 1170 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (8846 8846
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (8846 8846
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (8846 8846
           (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (8846 8846
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (8846 8846
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (8846 8846
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (8846 8846
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (8846 8846
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (8846 8846
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (7820 136 (:LINEAR FLOOR-BOUNDS-1))
     (7686 206 (:REWRITE MOD-ZERO . 2))
     (7196 288
           (:REWRITE STR::CHARACTER-LISTP-WHEN-OCTAL-DIGIT-LISTP))
     (7196 288
           (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-LISTP))
     (7154 206 (:REWRITE CANCEL-MOD-+))
     (6930 6930
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (6930 6930
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (6930 6930
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (6930 6930
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (6920 406 (:REWRITE CANCEL-FLOOR-+))
     (6604 288
           (:REWRITE STR::CHARACTER-LISTP-WHEN-DIGIT-LISTP))
     (5160 950 (:REWRITE |(* y x)|))
     (4552 1832
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (3280 4
           (:REWRITE STR::OCTAL-DIGIT-LISTP-OF-CONS))
     (3280 4
           (:REWRITE STR::HEX-DIGIT-LISTP-OF-CONS))
     (3264 4 (:REWRITE STR::DIGIT-LISTP-OF-CONS))
     (2864 76 (:REWRITE ZP-OPEN))
     (2310 950 (:REWRITE DEFAULT-*-2))
     (2204 292
           (:REWRITE STR::OCTAL-DIGIT-LISTP-WHEN-NOT-CONSP))
     (2204 292
           (:REWRITE STR::HEX-DIGIT-LISTP-WHEN-NOT-CONSP))
     (2204 292
           (:REWRITE STR::DIGIT-LISTP-WHEN-NOT-CONSP))
     (2176 68 (:REWRITE FLOOR-FLOOR-INTEGER-ALT))
     (1832 1832
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1832 1832
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (1832 1832
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (1806 406 (:REWRITE FLOOR-ZERO . 3))
     (1566 206 (:REWRITE MOD-ZERO . 3))
     (1566 206 (:REWRITE MOD-X-Y-=-X . 4))
     (1288 608
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1288 608 (:REWRITE DEFAULT-<-1))
     (1224 68 (:REWRITE FLOOR-POSITIVE . 1))
     (1202 1202 (:REWRITE |(equal (- x) (- y))|))
     (1100 144 (:REWRITE DEFAULT-CDR))
     (1100 144 (:REWRITE DEFAULT-CAR))
     (1092 412 (:REWRITE MOD-COMPLETION))
     (950 950
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (950 950 (:REWRITE DEFAULT-*-1))
     (890 890
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (886 206 (:REWRITE MOD-NEG))
     (886 206 (:REWRITE MOD-CANCEL-*))
     (814 814 (:REWRITE REDUCE-INTEGERP-+))
     (814 814 (:REWRITE INTEGERP-MINUS-X))
     (814 814 (:REWRITE |(integerp (* c x))|))
     (814 814 (:META META-INTEGERP-CORRECT))
     (716 716
          (:TYPE-PRESCRIPTION STR::OCTAL-DIGIT-LISTP))
     (716 716
          (:TYPE-PRESCRIPTION STR::HEX-DIGIT-LISTP))
     (716 716
          (:TYPE-PRESCRIPTION STR::DIGIT-LISTP))
     (612 68 (:REWRITE |(+ y x)|))
     (608 608 (:REWRITE SIMPLIFY-SUMS-<))
     (608 608
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (608 608
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (608 608 (:REWRITE DEFAULT-<-2))
     (608 608 (:REWRITE |(< (- x) (- y))|))
     (584 584
          (:REWRITE STR::OCTAL-DIGIT-LISTP-WHEN-SUBSETP-EQUAL))
     (584 584
          (:REWRITE STR::HEX-DIGIT-LISTP-WHEN-SUBSETP-EQUAL))
     (408 406 (:REWRITE FLOOR-COMPLETION))
     (406 406 (:REWRITE FLOOR-ZERO . 4))
     (406 406 (:REWRITE FLOOR-ZERO . 2))
     (406 406 (:REWRITE FLOOR-MINUS-WEAK))
     (406 406 (:REWRITE FLOOR-MINUS-2))
     (406 406 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (340 68 (:REWRITE DEFAULT-+-2))
     (340 68 (:LINEAR FLOOR-BOUNDS-3))
     (340 68 (:LINEAR FLOOR-BOUNDS-2))
     (280 140
          (:REWRITE STR::OCTAL-DIGIT-LISTP-OF-CDR-WHEN-OCTAL-DIGIT-LISTP))
     (280 140
          (:REWRITE STR::HEX-DIGIT-LISTP-OF-CDR-WHEN-HEX-DIGIT-LISTP))
     (280 140
          (:REWRITE STR::DIGIT-LISTP-OF-CDR-WHEN-DIGIT-LISTP))
     (218 206 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (218 206 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (206 206 (:REWRITE MOD-X-Y-=-X . 2))
     (206 206 (:REWRITE MOD-MINUS-2))
     (204 204
          (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (68 68
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (68 68 (:REWRITE NORMALIZE-ADDENDS))
     (68 68 (:REWRITE FLOOR-POSITIVE . 3))
     (68 68 (:REWRITE FLOOR-POSITIVE . 2))
     (68 68 (:REWRITE DEFAULT-+-1))
     (40 40 (:REWRITE SUBSETP-MEMBER . 4))
     (40 40 (:REWRITE SUBSETP-MEMBER . 3))
     (40 40 (:REWRITE SUBSETP-MEMBER . 2))
     (40 40 (:REWRITE SUBSETP-MEMBER . 1))
     (16 2 (:REWRITE DEFAULT-UNARY-/))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (8 8
        (:REWRITE STR::OCTAL-DIGITP-WHEN-MEMBER-EQUAL-OF-OCTAL-DIGIT-LISTP))
     (8 8
        (:REWRITE STR::HEX-DIGITP-WHEN-MEMBER-EQUAL-OF-HEX-DIGIT-LISTP))
     (8 8 (:REWRITE |(equal (- x) 0)|))
     (8 4
        (:REWRITE STR::OCTAL-DIGITP-WHEN-NONZERO-OCTAL-DIGITP))
     (8 4
        (:REWRITE STR::HEX-DIGITP-WHEN-NONZERO-HEX-DIGITP))
     (8 4
        (:REWRITE STR::DIGITP-WHEN-NONZERO-DIGITP))
     (4 4
        (:TYPE-PRESCRIPTION STR::OCTAL-DIGITP$INLINE))
     (4 4
        (:TYPE-PRESCRIPTION STR::NONZERO-OCTAL-DIGITP$INLINE))
     (4 4
        (:TYPE-PRESCRIPTION STR::NONZERO-HEX-DIGITP$INLINE))
     (4 4
        (:TYPE-PRESCRIPTION STR::NONZERO-DIGITP$INLINE))
     (4 4
        (:TYPE-PRESCRIPTION STR::HEX-DIGITP$INLINE))
     (4 4
        (:TYPE-PRESCRIPTION STR::DIGITP$INLINE))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX)))
(STR::__PRETTY-NUMBER-AUX
     (12644 7
            (:DEFINITION EXPLODE-NONNEGATIVE-INTEGER))
     (9982 7 (:DEFINITION DIGIT-TO-CHAR))
     (3296 664 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (3296 664
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2003 109 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2003 109
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2003 109
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1358 1358
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (1358 1358
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1358 1358
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1358 1358
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (859 31 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (752 20 (:REWRITE CANCEL-FLOOR-+))
     (664 664 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (664 664
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (664 664
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (664 664
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (664 664
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (534 6 (:REWRITE REWRITE-FLOOR-MOD-WEAK))
     (408 75 (:REWRITE |(* y x)|))
     (363 25 (:REWRITE MOD-ZERO . 2))
     (362 6
          (:REWRITE STR::CHARACTER-LISTP-WHEN-OCTAL-DIGIT-LISTP))
     (362 6
          (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-LISTP))
     (340 6
          (:REWRITE STR::CHARACTER-LISTP-WHEN-DIGIT-LISTP))
     (330 7 (:REWRITE ZP-OPEN))
     (324 108
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (315 87 (:REWRITE DEFAULT-*-2))
     (315 11
          (:REWRITE STR::OCTAL-DIGIT-LISTP-WHEN-NOT-CONSP))
     (315 11
          (:REWRITE STR::HEX-DIGIT-LISTP-WHEN-NOT-CONSP))
     (315 11
          (:REWRITE STR::DIGIT-LISTP-WHEN-NOT-CONSP))
     (291 25 (:REWRITE CANCEL-MOD-+))
     (189 7 (:REWRITE DEFAULT-CDR))
     (186 15 (:REWRITE DEFAULT-+-2))
     (141 3 (:DEFINITION LEN))
     (128 20 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (126 4 (:REWRITE DEFAULT-CAR))
     (124 5
          (:REWRITE STR::OCTAL-DIGIT-LISTP-OF-CONS))
     (124 5
          (:REWRITE STR::HEX-DIGIT-LISTP-OF-CONS))
     (114 6 (:REWRITE DEFAULT-UNARY-MINUS))
     (114 5 (:REWRITE STR::DIGIT-LISTP-OF-CONS))
     (109 109 (:REWRITE |(equal (- x) (- y))|))
     (108 108
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (108 108
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (108 108
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (108 6 (:REWRITE MOD-POSITIVE . 1))
     (105 105 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (90 6 (:REWRITE |(- (* c x))|))
     (87 87
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (87 87 (:REWRITE DEFAULT-*-1))
     (75 15 (:REWRITE DEFAULT-+-1))
     (58 58 (:REWRITE REDUCE-INTEGERP-+))
     (58 58 (:REWRITE INTEGERP-MINUS-X))
     (58 58 (:META META-INTEGERP-CORRECT))
     (51 51 (:REWRITE |(integerp (* c x))|))
     (50 50 (:REWRITE MOD-COMPLETION))
     (37 37
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (36 25 (:REWRITE MOD-X-Y-=-X . 3))
     (36 6 (:REWRITE |(+ y (+ x z))|))
     (33 21 (:REWRITE NORMALIZE-ADDENDS))
     (31 31 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (30 30 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (30 30 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (30 30 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (30 30
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (30 30
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (30 30
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (30 30
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (30 30
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (25 25 (:REWRITE MOD-ZERO . 3))
     (25 25 (:REWRITE MOD-X-Y-=-X . 4))
     (25 25 (:REWRITE MOD-X-Y-=-X . 2))
     (25 25 (:REWRITE MOD-NEG))
     (25 25 (:REWRITE MOD-MINUS-2))
     (25 25 (:REWRITE MOD-CANCEL-*))
     (25 14 (:REWRITE FLOOR-ZERO . 3))
     (22 22
         (:REWRITE STR::OCTAL-DIGIT-LISTP-WHEN-SUBSETP-EQUAL))
     (22 22
         (:REWRITE STR::HEX-DIGIT-LISTP-WHEN-SUBSETP-EQUAL))
     (21 21 (:REWRITE SIMPLIFY-SUMS-<))
     (21 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (21 21 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (21 21 (:REWRITE DEFAULT-<-2))
     (21 21 (:REWRITE DEFAULT-<-1))
     (21 21 (:REWRITE |(< (- x) (- y))|))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14 (:REWRITE FLOOR-ZERO . 4))
     (14 14 (:REWRITE FLOOR-ZERO . 2))
     (14 14 (:REWRITE FLOOR-MINUS-WEAK))
     (14 14 (:REWRITE FLOOR-MINUS-2))
     (14 14 (:REWRITE FLOOR-COMPLETION))
     (14 2 (:REWRITE |(< x (if a b c))|))
     (13 13
         (:TYPE-PRESCRIPTION STR::OCTAL-DIGIT-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION STR::HEX-DIGIT-LISTP))
     (13 13
         (:TYPE-PRESCRIPTION STR::DIGIT-LISTP))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (12 12 (:REWRITE |(< (- x) 0)|))
     (12 6 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (12 6 (:REWRITE |(+ y x)|))
     (6 6 (:REWRITE MOD-POSITIVE . 3))
     (6 6 (:REWRITE MOD-POSITIVE . 2))
     (6 6 (:REWRITE |(+ x (- x))|))
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (6 6 (:REWRITE |(+ 0 x)|))
     (6 6 (:REWRITE |(* (- x) y)|))
     (6 2 (:REWRITE |(* (if a b c) x)|))
     (4 4
        (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
     (4 4
        (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (3 3 (:LINEAR LISTPOS-COMPLETE))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (2 2 (:REWRITE |(< 0 (- x))|))
     (2 2
        (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
     (2 1
        (:REWRITE STR::OCTAL-DIGIT-LISTP-OF-CDR-WHEN-OCTAL-DIGIT-LISTP))
     (2 1
        (:REWRITE STR::HEX-DIGIT-LISTP-OF-CDR-WHEN-HEX-DIGIT-LISTP))
     (2 1
        (:REWRITE STR::DIGIT-LISTP-OF-CDR-WHEN-DIGIT-LISTP))
     (1 1 (:REWRITE MOD-NEGATIVE . 3))
     (1 1 (:REWRITE MOD-NEGATIVE . 2))
     (1 1 (:REWRITE FLOOR-NEGATIVE . 3))
     (1 1 (:REWRITE FLOOR-NEGATIVE . 2)))
(STR::PRETTY-NUMBER)
(STR::DWIM-STRING-FIX)
(STR::DWIM-STRING-LIST-FIX)
(STR::STRING-LISTP-OF-DWIM-STRING-LIST-FIX (11 10 (:REWRITE DEFAULT-CAR))
                                           (10 9 (:REWRITE DEFAULT-CDR)))
(STR::CAT-LIST)
(STR::CAT-LIST-WITH-SEPARATOR)
(STR::EXPLODE-LIST (2 2 (:REWRITE DEFAULT-CAR))
                   (1 1 (:REWRITE DEFAULT-CDR)))
(STR::CHAR-LIST-REPLACE)
(STR::CHAR-LIST-REPLACE-CHAR-LIST)
(STR::CHAR-LIST-REPLACE-PATTERNS)
(STR::STRING-REPLACE-PATTERNS)
