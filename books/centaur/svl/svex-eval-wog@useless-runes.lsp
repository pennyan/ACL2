(SVL::SVEX-KIND-WOG$INLINE)
(SVL::SVEX-KIND-WOG-IS-SVEX-KIND)
(SVL::SVEX-ENV-FASTLOOKUP-WOG)
(SVL::4VEC-P-OF-SVEX-ENV-FASTLOOKUP-WOG
     (16 16 (:REWRITE DEFAULT-CAR))
     (16 4 (:REWRITE O-P-O-INFP-CAR))
     (10 10 (:REWRITE DEFAULT-CDR))
     (10 2
         (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (8 8 (:TYPE-PRESCRIPTION O-P))
     (7 1
        (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (4 4 (:REWRITE O-P-DEF-O-FINP-1))
     (4 4
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (3 3 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (2 2
        (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP)))
(SVL::SVEX-ENV-LOOKUP-IS-SVEX-ENV-FASTLOOKUP-WOG
 (4091 19
       (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (4080 15 (:DEFINITION APPLY$-BADGEP))
 (3516 16 (:DEFINITION SUBSETP-EQUAL))
 (3196 120 (:DEFINITION MEMBER-EQUAL))
 (2004 64
       (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (1914 1906 (:REWRITE DEFAULT-CAR))
 (1746 40 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
 (1659 1633 (:REWRITE DEFAULT-CDR))
 (1220 305 (:REWRITE O-P-O-INFP-CAR))
 (910 184
      (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (649 105
      (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (649 105
      (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (649 105
      (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (598 97
      (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (535 105
      (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (441 111
      (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (368 368
      (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (305 305 (:REWRITE O-P-DEF-O-FINP-1))
 (254 254
      (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (240 240 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (239 239
      (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (210 210
      (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (210 210
      (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (210 210
      (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (208 208 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (192 192
      (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (172 172
      (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (128 128
      (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (114 19
      (:REWRITE SV::SVEX-ALIST-P-OF-CDR-WHEN-SVEX-ALIST-P))
 (114 19
      (:REWRITE SV::SVAR-MAP-P-OF-CDR-WHEN-SVAR-MAP-P))
 (114 19
      (:REWRITE SV::SVAR-ALIST-P-OF-CDR-WHEN-SVAR-ALIST-P))
 (113 113
      (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (112 112 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (105 105
      (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (105 105
      (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (105 105
      (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 (100 8 (:DEFINITION NATP))
 (96 24
     (:REWRITE SV::SVAR-BOOLMASKS-P-OF-CDR-WHEN-SVAR-BOOLMASKS-P))
 (92 14
     (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
 (86 86
     (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (81 15 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (71 7 (:DEFINITION SV::2VEC-P$INLINE))
 (66 16
     (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (59 59 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (46 4 (:DEFINITION TRUE-LISTP))
 (40 40
     (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
 (40 16
     (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (40
    7
    (:REWRITE SV::INTEGERP-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-SVAR-BOOLMASKS-P))
 (37 37
     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (30 4 (:DEFINITION LEN))
 (28 28 (:TYPE-PRESCRIPTION LEN))
 (24 4 (:DEFINITION ALL-NILS))
 (20 20 (:TYPE-PRESCRIPTION ALL-NILS))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 16 (:LINEAR LEN-WHEN-PREFIXP))
 (14 14
     (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
 (10 4
     (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (10 4
     (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (8 8
    (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
 (8 8 (:LINEAR BOUNDS-POSITION-EQUAL))
 (8 4 (:REWRITE O-INFP->NEQ-0))
 (8 4 (:REWRITE DEFAULT-+-2))
 (7 7
    (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
 (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (4 4 (:REWRITE DEFAULT-+-1)))
(SVL::4VEC-FIX-WOG)
(SVL::4VEC-P-OF-4VEC-FIX-WOG (22 22 (:REWRITE DEFAULT-CDR))
                             (22 22 (:REWRITE DEFAULT-CAR))
                             (10 10 (:REWRITE O-INFP->NEQ-0))
                             (10 10
                                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(SVL::4VEC-FIX-WOG-IS-4VEC-FIX
     (17 1 (:REWRITE SV::4VEC-FIX-OF-4VEC))
     (9 9
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 1 (:DEFINITION SV::4VEC-P))
     (5 1
        (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-CAR))
     (2 2 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (2 2 (:TYPE-PRESCRIPTION SV::4VEC-P))
     (2 2
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (2 1
        (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P)))
(SVL::SVEX-APPLY-COLLECT-ARGS2
     (40 37 (:REWRITE DEFAULT-<-1))
     (37 37 (:REWRITE DEFAULT-<-2))
     (23 23 (:REWRITE DEFAULT-+-2))
     (23 23 (:REWRITE DEFAULT-+-1))
     (15 5 (:REWRITE O<=-O-FINP-DEF))
     (9 9
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 2 (:REWRITE O-FIRST-EXPT-<))
     (5 5 (:REWRITE |a < b & b < c  =>  a < c|))
     (5 5 (:REWRITE O-INFP-O-FINP-O<=))
     (5 5 (:REWRITE AC-<))
     (4 4 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2 (:REWRITE O-FIRST-COEFF-<))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (1 1
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(SVL::SVEX-APPLY-CASES-FN-WOG)
(SVL::SVEX-APPLY-WOG)
(SVL::4VEC-P-OF-SVEX-APPLY-WOG)
(SVL::SVEX-APPLY-IS-SVEX-APPLY-WOG
 (4637 416
       (:REWRITE SV::4VECLIST-FIX-WHEN-4VECLIST-P))
 (2151 381
       (:REWRITE SV::4VECLIST-P-OF-CDR-WHEN-4VECLIST-P))
 (1997 1338 (:REWRITE DEFAULT-CDR))
 (1494 1494
       (:REWRITE SV::4VECLIST-P-WHEN-SUBSETP-EQUAL))
 (974 974
      (:REWRITE SV::CAR-OF-4VECLIST-FIX-X-NORMALIZE-CONST-UNDER-4VEC-EQUIV))
 (928 928 (:REWRITE DEFAULT-CAR))
 (907 303
      (:REWRITE SV::FNSYM-FIX-WHEN-FNSYM-P))
 (747 747
      (:REWRITE SV::4VECLIST-P-WHEN-NOT-CONSP))
 (742 742 (:REWRITE NTH-WHEN-PREFIXP))
 (604 604 (:TYPE-PRESCRIPTION SV::FNSYM-P))
 (466
   466
   (:REWRITE SV::CDR-OF-4VECLIST-FIX-X-NORMALIZE-CONST-UNDER-4VECLIST-EQUIV))
 (28 28
     (:REWRITE SV::4VEC-REV-BLOCKS-OF-4VEC-FIX-NBITS-NORMALIZE-CONST))
 (28 28
     (:REWRITE SV::4VEC-CONCAT-OF-2VECNATX-FIX-WIDTH-NORMALIZE-CONST))
 (28 28
     (:REWRITE SV::4VEC-BIT?-OF-3VEC-FIX-TESTS-NORMALIZE-CONST))
 (28 28
     (:REWRITE SV::4VEC-?-OF-3VEC-FIX-TEST-NORMALIZE-CONST))
 (28 28
     (:REWRITE SV::4VEC-?*-OF-3VEC-FIX-TEST-NORMALIZE-CONST))
 (18 18
     (:REWRITE SV::4VEC-ZERO-EXT-OF-4VEC-FIX-N-NORMALIZE-CONST))
 (18 18
     (:REWRITE SV::4VEC-WILDEQ-SAFE-OF-3VEC-FIX-A-NORMALIZE-CONST))
 (18 18
     (:REWRITE SV::4VEC-SYMWILDEQ-OF-4VEC-FIX-A-NORMALIZE-CONST))
 (18 18
     (:REWRITE SV::4VEC-SIGN-EXT-OF-4VEC-FIX-N-NORMALIZE-CONST))
 (18 18
     (:REWRITE SV::4VEC-RSH-OF-2VECX-FIX-AMT-NORMALIZE-CONST))
 (18 18
     (:REWRITE SV::4VEC-RESOR-OF-4VEC-FIX-A-NORMALIZE-CONST))
 (18 18
     (:REWRITE SV::4VEC-RESAND-OF-4VEC-FIX-A-NORMALIZE-CONST))
 (18 18
     (:REWRITE SV::4VEC-RES-OF-4VEC-FIX-A-NORMALIZE-CONST))
 (18 18
     (:REWRITE SV::4VEC-OVERRIDE-OF-4VEC-FIX-STRONGER-NORMALIZE-CONST))
 (18 18
     (:REWRITE SV::4VEC-LSH-OF-2VECX-FIX-AMT-NORMALIZE-CONST))
 (18 18
     (:REWRITE SV::4VEC-BIT-EXTRACT-OF-4VEC-FIX-N-NORMALIZE-CONST))
 (18 18
     (:REWRITE SV::4VEC-===-OF-4VEC-FIX-X-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-WILDEQ-OF-3VEC-FIX-B-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-WILDEQ-OF-3VEC-FIX-A-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-TIMES-OF-2VECX-FIX-Y-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-TIMES-OF-2VECX-FIX-X-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-REMAINDER-OF-2VECX-FIX-Y-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-REMAINDER-OF-2VECX-FIX-X-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-QUOTIENT-OF-2VECX-FIX-Y-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-QUOTIENT-OF-2VECX-FIX-X-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-POW-OF-2VECX-FIX-EXP-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-POW-OF-2VECX-FIX-BASE-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-PLUS-OF-2VECX-FIX-Y-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-PLUS-OF-2VECX-FIX-X-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-MINUS-OF-2VECX-FIX-Y-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-MINUS-OF-2VECX-FIX-X-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-BITXOR-OF-3VEC-FIX-Y-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-BITXOR-OF-3VEC-FIX-X-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-BITOR-OF-3VEC-FIX-Y-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-BITOR-OF-3VEC-FIX-X-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-BITAND-OF-3VEC-FIX-Y-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-BITAND-OF-3VEC-FIX-X-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-==-OF-3VEC-FIX-Y-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-==-OF-3VEC-FIX-X-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-<-OF-2VECX-FIX-Y-NORMALIZE-CONST))
 (16 16
     (:REWRITE SV::4VEC-<-OF-2VECX-FIX-X-NORMALIZE-CONST))
 (6 2 (:REWRITE SV::3VEC-FIX-OF-3VEC-P))
 (4 4 (:TYPE-PRESCRIPTION SV::3VEC-P))
 (2 2
    (:REWRITE SV::4VEC-XDET-OF-2VECX-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE SV::4VEC-UMINUS-OF-2VECX-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE SV::4VEC-REDUCTION-OR-OF-3VEC-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE SV::4VEC-REDUCTION-AND-OF-3VEC-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE SV::4VEC-PARITY-OF-2VECX-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE SV::4VEC-ONSET-OF-4VEC-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE SV::4VEC-ONEHOT-OF-2VECX-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE SV::4VEC-OFFSET-OF-4VEC-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE SV::4VEC-COUNTONES-OF-2VECX-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE SV::4VEC-CLOG2-OF-2VECNATX-FIX-A-NORMALIZE-CONST))
 (2 2
    (:REWRITE SV::4VEC-BITNOT-OF-3VEC-FIX-X-NORMALIZE-CONST))
 (2 2
    (:REWRITE SV::3VEC-FIX-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(SVL::RETURNS-LEMMA1
     (23 2
         (:REWRITE SV::SVEX-P-WHEN-MAYBE-SVEX-P))
     (20 4
         (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (20 1
         (:REWRITE SV::MAYBE-SVEX-P-WHEN-SVEX-P))
     (14 2
         (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (8 8
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (6 6 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (4 4
        (:REWRITE SV::SVEX-P-WHEN-MEMBER-EQUAL-OF-SVEXLIST-P))
     (3 3 (:TYPE-PRESCRIPTION SV::MAYBE-SVEX-P))
     (1 1
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (1 1
        (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP)))
(SVL::RETURNS-LEMMA2
     (84 2
         (:REWRITE SV::SVEX-P-WHEN-MAYBE-SVEX-P))
     (81 1
         (:REWRITE SV::MAYBE-SVEX-P-WHEN-SVEX-P))
     (52 4
         (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (46 2
         (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (32 4
         (:REWRITE SV::INTEGERP-OF-CDAR-WHEN-SVAR-BOOLMASKS-P))
     (26 4
         (:REWRITE SV::4VEC-P-OF-CAR-WHEN-4VECLIST-P))
     (22 22 (:REWRITE DEFAULT-CAR))
     (18 18 (:REWRITE DEFAULT-CDR))
     (16 4
         (:REWRITE SV::SVAR-BOOLMASKS-P-OF-CDR-WHEN-SVAR-BOOLMASKS-P))
     (14 4 (:REWRITE SVL::RETURNS-LEMMA1))
     (12 2
         (:REWRITE SV::4VECLIST-P-OF-CDR-WHEN-4VECLIST-P))
     (8 8
        (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
     (8 8
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (8 8
        (:REWRITE SV::4VECLIST-P-WHEN-SUBSETP-EQUAL))
     (8 8
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (8 2 (:REWRITE O-P-O-INFP-CAR))
     (6 6 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (4 4
        (:REWRITE SV::SVEX-P-WHEN-MEMBER-EQUAL-OF-SVEXLIST-P))
     (4 4
        (:REWRITE SV::4VECLIST-P-WHEN-NOT-CONSP))
     (3 3 (:TYPE-PRESCRIPTION SV::MAYBE-SVEX-P))
     (3 3 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (2 2 (:REWRITE O-P-DEF-O-FINP-1))
     (1 1
        (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP)))
(SVL::SVEX-EVAL-WOG (69 42 (:REWRITE RP::MEASURE-LEMMA1))
                    (45 3 (:DEFINITION RP::EX-FROM-RP))
                    (26 8 (:REWRITE DEFAULT-CDR))
                    (21 9 (:REWRITE DEFAULT-CAR))
                    (20 6 (:REWRITE RP::CONS-COUNT-ATOM))
                    (16 16 (:REWRITE RP::MEASURE-LEMMA1-2))
                    (4 1 (:REWRITE O-P-O-INFP-CAR))
                    (3 3 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                    (1 1
                       (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                    (1 1 (:REWRITE O-P-DEF-O-FINP-1))
                    (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(SVL::SVEX-EVAL-WOG-FLAG (69 42 (:REWRITE RP::MEASURE-LEMMA1))
                         (45 3 (:DEFINITION RP::EX-FROM-RP))
                         (26 8 (:REWRITE DEFAULT-CDR))
                         (21 9 (:REWRITE DEFAULT-CAR))
                         (20 6 (:REWRITE RP::CONS-COUNT-ATOM))
                         (16 16 (:REWRITE RP::MEASURE-LEMMA1-2))
                         (12 2 (:TYPE-PRESCRIPTION RETURN-LAST))
                         (4 1 (:REWRITE O-P-O-INFP-CAR))
                         (3 3 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                         (2 2
                            (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
                         (1 1
                            (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                         (1 1 (:REWRITE O-P-DEF-O-FINP-1))
                         (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(FLAG::FLAG-EQUIV-LEMMA)
(SVL::SVEX-EVAL-WOG-FLAG-EQUIVALENCES)
(SVL::FLAG-LEMMA-FOR-RETURN-TYPE-OF-SVEX-EVAL-WOG.VAL
     (406 74
          (:REWRITE SV::SVEX-P-WHEN-MAYBE-SVEX-P))
     (378 69
          (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (357 5 (:DEFINITION SUBSETP-EQUAL))
     (296 37
          (:REWRITE SV::MAYBE-SVEX-P-WHEN-SVEX-P))
     (290 10
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (273 35
          (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (246 138
          (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (180 10 (:DEFINITION LOOP$-AS))
     (110 110
          (:TYPE-PRESCRIPTION SV::MAYBE-SVEX-P))
     (103 103
          (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (101 100 (:REWRITE DEFAULT-CDR))
     (78 77 (:REWRITE DEFAULT-CAR))
     (70 18
         (:REWRITE SV::4VECLIST-P-WHEN-NOT-CONSP))
     (60 10 (:DEFINITION CDR-LOOP$-AS-TUPLE))
     (60 10 (:DEFINITION CAR-LOOP$-AS-TUPLE))
     (50 10 (:DEFINITION EMPTY-LOOP$-AS-TUPLEP))
     (48 48
         (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
     (46 46 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (31 31 (:REWRITE CDR-CONS))
     (31 31 (:REWRITE CAR-CONS))
     (24 24 (:TYPE-PRESCRIPTION LOOP$-AS))
     (18 9 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (12 12
         (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
     (12 12
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (12 12
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2)))
(SVL::RETURN-TYPE-OF-SVEX-EVAL-WOG.VAL)
(SVL::RETURN-TYPE-OF-SVEXLIST-EVAL-WOG.VALS)
(SVL::TRUE-LISTP-OF-SVEXLIST-EVAL-WOG)
(SVL::CONSP-OF-SVEXLIST-EVAL (24 1 (:DEFINITION SVL::SVEX-EVAL-WOG))
                             (13 4 (:REWRITE O-P-O-INFP-CAR))
                             (11 7 (:REWRITE DEFAULT-CAR))
                             (9 1
                                (:DEFINITION SVL::SVEX-KIND-WOG$INLINE))
                             (7 6 (:REWRITE DEFAULT-CDR))
                             (6 6 (:TYPE-PRESCRIPTION O-P))
                             (3 3 (:REWRITE O-P-DEF-O-FINP-1))
                             (1 1
                                (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                             (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(SVL::UPPER-LOWER-OF-3VEC-FIX
     (6 2
        (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (3 1 (:DEFINITION SV::2VEC-P$INLINE))
     (2 2
        (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (1 1
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(SVL::4VEC-?-CASES
     (26 4
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (20 2 (:DEFINITION SV::2VEC-P$INLINE))
     (18 2 (:REWRITE SV::4VEC-FIX-OF-4VEC))
     (7 3 (:REWRITE SV::3VEC-FIX-OF-3VEC-P))
     (7 1 (:REWRITE SVL::RETURNS-LEMMA1))
     (5 1
        (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (5 1
        (:DEFINITION SVL::SVEX-KIND-WOG$INLINE))
     (4 4
        (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (3 3 (:TYPE-PRESCRIPTION SV::4VEC-P))
     (3 3
        (:REWRITE SV::3VEC-FIX-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (2 2
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (2 1
        (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (1 1
        (:TYPE-PRESCRIPTION SVL::SVEX-KIND-WOG$INLINE))
     (1 1
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(SVL::4VEC-BIT?-CASES
     (1680 24 (:DEFINITION FLOOR))
     (944 48
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (522 346 (:REWRITE DEFAULT-+-2))
     (452 346 (:REWRITE DEFAULT-+-1))
     (256 48 (:REWRITE COMMUTATIVITY-OF-*))
     (232 24 (:DEFINITION EVENP))
     (196 126 (:REWRITE DEFAULT-UNARY-MINUS))
     (192 48 (:DEFINITION NFIX))
     (152 124 (:REWRITE DEFAULT-*-2))
     (144 120 (:REWRITE DEFAULT-<-1))
     (136 120 (:REWRITE DEFAULT-<-2))
     (124 124 (:REWRITE DEFAULT-*-1))
     (120 120
          (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (120 16
          (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (112 16 (:REWRITE DISTRIBUTIVITY))
     (92 8 (:DEFINITION SV::2VEC-P$INLINE))
     (72 72
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (72 24 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (72 24
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (68 34 (:REWRITE O-INFP->NEQ-0))
     (38 6 (:REWRITE SVL::RETURNS-LEMMA1))
     (34 2 (:REWRITE SV::4VEC-FIX-OF-4VEC))
     (32 24 (:REWRITE DEFAULT-NUMERATOR))
     (32 24 (:REWRITE DEFAULT-DENOMINATOR))
     (30 2
         (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X))
     (22 4
         (:DEFINITION SVL::SVEX-KIND-WOG$INLINE))
     (20 20
         (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (18 6
         (:REWRITE SVL::UPPER-LOWER-OF-3VEC-FIX))
     (12 12 (:TYPE-PRESCRIPTION SV::3VEC-P))
     (12 12
         (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (10 10
         (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (8 8 (:REWRITE DEFAULT-CAR))
     (4 4
        (:TYPE-PRESCRIPTION SVL::SVEX-KIND-WOG$INLINE))
     (4 4 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
     (2 2
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(SVL::4VEC-?*-CASES
     (26 4
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (20 2 (:DEFINITION SV::2VEC-P$INLINE))
     (18 2 (:REWRITE SV::4VEC-FIX-OF-4VEC))
     (7 3 (:REWRITE SV::3VEC-FIX-OF-3VEC-P))
     (7 1 (:REWRITE SVL::RETURNS-LEMMA1))
     (5 1
        (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
     (5 1
        (:DEFINITION SVL::SVEX-KIND-WOG$INLINE))
     (4 4
        (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (3 3 (:TYPE-PRESCRIPTION SV::4VEC-P))
     (3 3
        (:REWRITE SV::3VEC-FIX-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 2 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 2
        (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
     (2 2
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (2 1
        (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
     (1 1
        (:TYPE-PRESCRIPTION SVL::SVEX-KIND-WOG$INLINE))
     (1 1
        (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
     (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(SVL::4VEC-BITAND-CASE
     (14 2
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (11 1 (:DEFINITION SV::2VEC-P$INLINE))
     (5 5
        (:TYPE-PRESCRIPTION SV::INTEGERP-OF-4VEC->UPPER))
     (3 3
        (:TYPE-PRESCRIPTION SV::INTEGERP-OF-4VEC->LOWER))
     (3 1 (:REWRITE SV::3VEC-FIX-OF-3VEC-P))
     (2 2 (:TYPE-PRESCRIPTION SV::3VEC-P))
     (2 2
        (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (1 1
        (:REWRITE SV::3VEC-FIX-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (1 1
        (:REWRITE SV::3VEC-BITAND-OF-4VEC-FIX-Y-NORMALIZE-CONST))
     (1 1
        (:REWRITE SV::3VEC-BITAND-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (1 1
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(SVL::4VEC-BITOR-CASE
     (14 2
         (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P))
     (11 1 (:DEFINITION SV::2VEC-P$INLINE))
     (6 4 (:REWRITE DEFAULT-+-2))
     (6 4 (:REWRITE DEFAULT-+-1))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 1 (:REWRITE SV::3VEC-FIX-OF-3VEC-P))
     (2 2 (:TYPE-PRESCRIPTION SV::3VEC-P))
     (2 2
        (:TYPE-PRESCRIPTION SV::2VEC-P$INLINE))
     (1 1
        (:REWRITE SV::3VEC-FIX-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (1 1
        (:REWRITE SV::3VEC-BITOR-OF-4VEC-FIX-Y-NORMALIZE-CONST))
     (1 1
        (:REWRITE SV::3VEC-BITOR-OF-4VEC-FIX-X-NORMALIZE-CONST))
     (1 1
        (:REWRITE SV::2VEC-P$INLINE-OF-4VEC-FIX-X-NORMALIZE-CONST)))
(SVL::SVEX-EVAL-WOG (3 3 (:REWRITE DEFAULT-CDR))
                    (2 2
                       (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                    (2 2 (:REWRITE DEFAULT-CAR))
                    (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE)))
(SVL::FLAG-LEMMA-FOR-SVEX-EVAL-WOG-IS-SVEX-EVAL
 (796 793 (:REWRITE DEFAULT-CDR))
 (426 414 (:REWRITE DEFAULT-CAR))
 (407 5 (:DEFINITION SUBSETP-EQUAL))
 (346 12
      (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (216 12 (:DEFINITION LOOP$-AS))
 (183 21
      (:REWRITE SV::4VEC-P-OF-CAR-WHEN-4VECLIST-P))
 (175 61 (:REWRITE O-P-O-INFP-CAR))
 (164 32
      (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (112 112 (:REWRITE DEFAULT-<-2))
 (112 112 (:REWRITE DEFAULT-<-1))
 (112 112 (:REWRITE DEFAULT-+-2))
 (112 112 (:REWRITE DEFAULT-+-1))
 (92 24
     (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (85 85
     (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (77 12
     (:REWRITE SV::4VECLIST-P-OF-CDR-WHEN-4VECLIST-P))
 (74 74
     (:REWRITE SV::SVEX-KIND$INLINE-OF-SVEX-FIX-X-NORMALIZE-CONST))
 (72 12 (:DEFINITION CDR-LOOP$-AS-TUPLE))
 (72 12 (:DEFINITION CAR-LOOP$-AS-TUPLE))
 (66 66
     (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (64 64 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (64 64
     (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (60 12 (:DEFINITION EMPTY-LOOP$-AS-TUPLEP))
 (58 58
     (:REWRITE SV::4VECLIST-P-WHEN-SUBSETP-EQUAL))
 (56 56
     (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (56 56 (:REWRITE DEFAULT-UNARY-MINUS))
 (38 38 (:REWRITE O-P-DEF-O-FINP-1))
 (36 36 (:REWRITE CDR-CONS))
 (36 36 (:REWRITE CAR-CONS))
 (33 33 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (30 5
     (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (29 29
     (:REWRITE SV::4VECLIST-P-WHEN-NOT-CONSP))
 (28 28 (:TYPE-PRESCRIPTION LOOP$-AS))
 (28 28 (:REWRITE O-INFP->NEQ-0))
 (24 8 (:REWRITE SV::FNSYM-FIX-WHEN-FNSYM-P))
 (21 21
     (:REWRITE SV::SVEXLIST-QUOTESP-OF-SVEXLIST-FIX-X-NORMALIZE-CONST))
 (21 21
     (:REWRITE SV::SVEXLIST-EVAL-WHEN-ATOM-CHEAP))
 (20 20 (:TYPE-PRESCRIPTION SV::FNSYM-P))
 (20 10 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
 (18 18
     (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (18 18
     (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (15
   15
   (:REWRITE SV::CDR-OF-SVEXLIST-FIX-X-NORMALIZE-CONST-UNDER-SVEXLIST-EQUIV))
 (14 14
     (:REWRITE SV::SVEXLIST-EVAL-OF-SVEXLIST-FIX-X-NORMALIZE-CONST))
 (14 14
     (:REWRITE SV::SVEXLIST-EVAL-OF-SVEX-ENV-FIX-ENV-NORMALIZE-CONST))
 (14 14
     (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (12 12
     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (11 11
     (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
 (11 11
     (:REWRITE SV::SVEX-VAR->NAME$INLINE-OF-SVEX-FIX-X-NORMALIZE-CONST))
 (11 11
     (:REWRITE SV::SVEX-EVAL-OF-SVEX-FIX-X-NORMALIZE-CONST))
 (11 11
     (:REWRITE SV::SVEX-EVAL-OF-SVEX-ENV-FIX-ENV-NORMALIZE-CONST))
 (11 11 (:REWRITE SV::SVEX-EVAL-OF-QUOTED))
 (10 10 (:TYPE-PRESCRIPTION BOOLEANP))
 (10 10
     (:REWRITE SV::SVEX-QUOTE->VAL$INLINE-OF-SVEX-FIX-X-NORMALIZE-CONST))
 (10 10
     (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (9 9
    (:REWRITE SV::SVEX-CALL->FN$INLINE-OF-SVEX-FIX-X-NORMALIZE-CONST))
 (9 9
    (:REWRITE SV::SVEX-CALL->ARGS$INLINE-OF-SVEX-FIX-X-NORMALIZE-CONST))
 (9
   9
   (:REWRITE SV::CDR-OF-4VECLIST-FIX-X-NORMALIZE-CONST-UNDER-4VECLIST-EQUIV))
 (9 9
    (:REWRITE SV::CAR-OF-4VECLIST-FIX-X-NORMALIZE-CONST-UNDER-4VEC-EQUIV))
 (8 8 (:REWRITE SV::SVAR-P-OF-SVAR-FIX))
 (7 7 (:DEFINITION EQ))
 (5 5
    (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (5 5
    (:REWRITE SV::CAR-OF-SVEXLIST-FIX-X-NORMALIZE-CONST-UNDER-SVEX-EQUIV))
 (1
  1
  (:REWRITE SV::CONS-OF-SVEXLIST-FIX-Y-NORMALIZE-CONST-UNDER-SVEXLIST-EQUIV))
 (1 1
    (:REWRITE SV::CONS-OF-SVEX-FIX-X-NORMALIZE-CONST-UNDER-SVEXLIST-EQUIV)))
(SVL::SVEX-EVAL-WOG-IS-SVEX-EVAL)
(SVL::SVEXLIST-EVAL-WOG-IS-SVEXLIST-EVAL)
(SVL::SVEX-EVAL-IS-SVEX-EVAL-WOG
     (10 2
         (:REWRITE SV::SVEX-P-WHEN-MAYBE-SVEX-P))
     (8 8
        (:TYPE-PRESCRIPTION SV::SVEX-KIND$INLINE))
     (8 2 (:REWRITE SV::SVEX-EVAL-WHEN-QUOTE))
     (7 2 (:REWRITE SV::SVEX-EVAL-WHEN-FNCALL))
     (7 1
        (:REWRITE SV::MAYBE-SVEX-P-WHEN-SVEX-P))
     (4 4
        (:REWRITE SV::SVEX-P-WHEN-MEMBER-EQUAL-OF-SVEXLIST-P))
     (4 1 (:DEFINITION EQ))
     (3 3 (:TYPE-PRESCRIPTION SV::MAYBE-SVEX-P))
     (2 2
        (:REWRITE SV::SVEX-KIND$INLINE-OF-SVEX-FIX-X-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::SVEX-EVAL-OF-SVEX-FIX-X-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::SVEX-EVAL-OF-SVEX-ENV-FIX-ENV-NORMALIZE-CONST))
     (2 2 (:REWRITE SV::SVEX-EVAL-OF-QUOTED))
     (1 1
        (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP)))
(SVL::SVEXLIST-EVAL-IS-SVEXLIST-EVAL-WOG
     (5 2
        (:REWRITE SV::SVEXLIST-UNQUOTE-CORRECT))
     (2 2
        (:TYPE-PRESCRIPTION SV::SVEXLIST-QUOTESP))
     (2 2
        (:REWRITE SV::SVEXLIST-P-WHEN-SUBSETP-EQUAL))
     (2 2
        (:REWRITE SV::SVEXLIST-EVAL-WHEN-ATOM-CHEAP))
     (2 2
        (:REWRITE SV::SVEXLIST-EVAL-OF-SVEXLIST-FIX-X-NORMALIZE-CONST))
     (2 2
        (:REWRITE SV::SVEXLIST-EVAL-OF-SVEX-ENV-FIX-ENV-NORMALIZE-CONST))
     (1 1
        (:REWRITE SV::SVEXLIST-QUOTESP-OF-SVEXLIST-FIX-X-NORMALIZE-CONST))
     (1 1
        (:REWRITE SV::SVEXLIST-P-WHEN-NOT-CONSP))
     (1 1
        (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP)))
(SVL::4VEC-LIST-LISTP)
(SVL::SVEX-LIST-LISTP)
(SVL::SVEXLIST-LIST-EVAL-WOG)
(SVL::4VEC-LIST-LISTP-OF-SVEXLIST-LIST-EVAL-WOG
     (478 22
          (:REWRITE SV::SVEXLIST-P-WHEN-SUBSETP-EQUAL))
     (436 4 (:DEFINITION SUBSETP-EQUAL))
     (312 20
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (236 8 (:DEFINITION MEMBER-EQUAL))
     (160 8 (:DEFINITION LOOP$-AS))
     (136 34 (:REWRITE O-P-O-INFP-CAR))
     (70 69 (:REWRITE DEFAULT-CDR))
     (69 68 (:REWRITE DEFAULT-CAR))
     (68 68 (:TYPE-PRESCRIPTION O-P))
     (64 64 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (56 8 (:DEFINITION EMPTY-LOOP$-AS-TUPLEP))
     (55 11
         (:REWRITE SV::SVEXLIST-P-WHEN-NOT-CONSP))
     (55 11
         (:REWRITE SV::4VECLIST-P-WHEN-NOT-CONSP))
     (48 8 (:DEFINITION CDR-LOOP$-AS-TUPLE))
     (48 8 (:DEFINITION CAR-LOOP$-AS-TUPLE))
     (34 34 (:REWRITE O-P-DEF-O-FINP-1))
     (32 32
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (32 32
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (28 28 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (22 22
         (:REWRITE SV::4VECLIST-P-WHEN-SUBSETP-EQUAL))
     (20 20 (:REWRITE SUBSETP-IMPLIES-MEMBER))
     (16 16 (:TYPE-PRESCRIPTION LOOP$-AS))
     (16 8 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
     (11 11
         (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
     (8 8
        (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL)))
