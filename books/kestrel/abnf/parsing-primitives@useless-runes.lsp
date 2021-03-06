(ABNF::PARSE-ANY (7 5 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
                 (5 1 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
                 (5 1
                    (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
                 (2 2 (:REWRITE DEFAULT-CAR))
                 (1 1 (:REWRITE DEFAULT-CDR))
                 (1 1
                    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                              . 2))
                 (1 1
                    (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                              . 1)))
(ABNF::MAYBE-MSGP-OF-PARSE-ANY.ERROR?
  (47 2
      (:REWRITE NAT-LIST-FIX-WHEN-NAT-LISTP))
  (33 2 (:DEFINITION NAT-LISTP))
  (26 1 (:REWRITE MAYBE-MSGP-WHEN-MSGP))
  (23 3
      (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
  (21 1 (:DEFINITION MSGP))
  (17 17 (:TYPE-PRESCRIPTION NAT-LISTP))
  (17 2
      (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
  (14 1 (:DEFINITION CHARACTER-ALISTP))
  (13 6 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
  (13 1 (:DEFINITION INTEGER-LISTP))
  (9 9
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 2))
  (9 9
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 1))
  (8 8 (:REWRITE DEFAULT-CAR))
  (7 7 (:TYPE-PRESCRIPTION INTEGER-LISTP))
  (7 2 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
  (6 6 (:REWRITE DEFAULT-CDR))
  (4 4 (:TYPE-PRESCRIPTION CHARACTER-ALISTP))
  (4 2
     (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
  (3 3 (:TYPE-PRESCRIPTION MSGP))
  (2 2 (:TYPE-PRESCRIPTION NATP))
  (2 2
     (:REWRITE MSGP-WHEN-MEMBER-EQUAL-OF-MSG-LISTP))
  (2 2
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
  (2 1
     (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
  (1 1 (:REWRITE DEFAULT-<-2))
  (1 1 (:REWRITE DEFAULT-<-1))
  (1 1
     (:REWRITE CDR-OF-NAT-LIST-FIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
  (1 1 (:DEFINITION NOT)))
(ABNF::NATP-OF-PARSE-ANY.NAT
   (47 2
       (:REWRITE NAT-LIST-FIX-WHEN-NAT-LISTP))
   (33 2 (:DEFINITION NAT-LISTP))
   (23 3
       (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
   (17 17 (:TYPE-PRESCRIPTION NAT-LISTP))
   (17 2
       (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
   (13 6 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
   (13 1 (:DEFINITION INTEGER-LISTP))
   (7 7 (:TYPE-PRESCRIPTION INTEGER-LISTP))
   (7 2 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
   (6 6
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 2))
   (6 6
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 1))
   (4 4 (:REWRITE DEFAULT-CDR))
   (4 4 (:REWRITE DEFAULT-CAR))
   (4 2
      (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
   (2 1
      (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
   (1 1 (:REWRITE DEFAULT-<-2))
   (1 1 (:REWRITE DEFAULT-<-1))
   (1 1
      (:REWRITE CDR-OF-NAT-LIST-FIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV)))
(ABNF::NAT-LISTP-OF-PARSE-ANY.REST-INPUT
    (93 3 (:DEFINITION NAT-LISTP))
    (70 5
        (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
    (63 4
        (:REWRITE NAT-LIST-FIX-WHEN-NAT-LISTP))
    (34 4
        (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
    (27 13 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
    (26 2 (:DEFINITION INTEGER-LISTP))
    (14 14 (:TYPE-PRESCRIPTION INTEGER-LISTP))
    (12 12
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
    (12 12
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
    (12 3 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
    (9 9 (:REWRITE DEFAULT-CAR))
    (8 4
       (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
    (7 7 (:REWRITE DEFAULT-CDR))
    (4 2
       (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
    (2 2 (:TYPE-PRESCRIPTION NATP))
    (2 2 (:REWRITE DEFAULT-<-2))
    (2 2 (:REWRITE DEFAULT-<-1))
    (2 2
       (:REWRITE CDR-OF-NAT-LIST-FIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
    (2 2 (:DEFINITION NOT)))
(ABNF::LEN-OF-PARSE-ANY-LINEAR-<=
   (230 6 (:REWRITE DEFAULT-<-1))
   (181 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
   (180 4
        (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
   (177 17
        (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
   (177 2 (:DEFINITION ACL2-NUMBER-LISTP))
   (161 9 (:DEFINITION RATIONAL-LISTP))
   (159 6
        (:REWRITE NAT-LIST-FIX-WHEN-NAT-LISTP))
   (114 9 (:DEFINITION NAT-LISTP))
   (97 10
       (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
   (87 5 (:DEFINITION INTEGER-LISTP))
   (71 12
       (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
   (63 63 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
   (60 14
       (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
   (53 53
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 2))
   (53 53
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 1))
   (52 52 (:TYPE-PRESCRIPTION NAT-LISTP))
   (47 47 (:REWRITE DEFAULT-CDR))
   (42 20
       (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
   (41 19 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
   (38 38 (:REWRITE DEFAULT-CAR))
   (33 33 (:TYPE-PRESCRIPTION INTEGER-LISTP))
   (24 12 (:REWRITE DEFAULT-+-2))
   (24 10
       (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
   (15 6 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
   (14 7
       (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
   (13 13
       (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
   (12 12 (:REWRITE DEFAULT-+-1))
   (10 4
       (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
   (9 6 (:REWRITE DEFAULT-<-2))
   (6 6 (:TYPE-PRESCRIPTION NATP))
   (6 3
      (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
   (4 4
      (:REWRITE CDR-OF-NAT-LIST-FIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV)))
(ABNF::LEN-OF-PARSE-ANY-LINEAR-<
   (230 6 (:REWRITE DEFAULT-<-1))
   (181 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
   (180 4
        (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
   (177 17
        (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
   (177 2 (:DEFINITION ACL2-NUMBER-LISTP))
   (161 9 (:DEFINITION RATIONAL-LISTP))
   (155 5
        (:REWRITE NAT-LIST-FIX-WHEN-NAT-LISTP))
   (114 9 (:DEFINITION NAT-LISTP))
   (97 10
       (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
   (87 5 (:DEFINITION INTEGER-LISTP))
   (71 12
       (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
   (63 63 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
   (60 14
       (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
   (52 52
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 2))
   (52 52
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 1))
   (51 51 (:TYPE-PRESCRIPTION NAT-LISTP))
   (47 47 (:REWRITE DEFAULT-CDR))
   (42 20
       (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
   (39 18 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
   (38 38 (:REWRITE DEFAULT-CAR))
   (33 33 (:TYPE-PRESCRIPTION INTEGER-LISTP))
   (24 12 (:REWRITE DEFAULT-+-2))
   (24 10
       (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
   (15 6 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
   (14 7
       (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
   (13 13
       (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
   (12 12 (:REWRITE DEFAULT-+-1))
   (10 4
       (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
   (9 6 (:REWRITE DEFAULT-<-2))
   (6 6 (:TYPE-PRESCRIPTION NATP))
   (6 3
      (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
   (4 4
      (:REWRITE CDR-OF-NAT-LIST-FIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV)))
(ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT
  (893 60
       (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
  (810 35 (:REWRITE DEFAULT-<-1))
  (689 30 (:DEFINITION INTEGER-LISTP))
  (564 56 (:DEFINITION NAT-LISTP))
  (554 15
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
  (538 14
       (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
  (521 37
       (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
  (491 7 (:DEFINITION ACL2-NUMBER-LISTP))
  (417 19 (:DEFINITION RATIONAL-LISTP))
  (391 221 (:REWRITE DEFAULT-CAR))
  (263 153 (:REWRITE DEFAULT-CDR))
  (251 251
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 2))
  (251 251
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 1))
  (232 60
       (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
  (214 51
       (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
  (188 95 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
  (130 40
       (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
  (86 24
      (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
  (81 34
      (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
  (54 14
      (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
  (42 18
      (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
  (35 35 (:REWRITE DEFAULT-<-2))
  (19 8
      (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
  (18 18 (:TYPE-PRESCRIPTION NATP))
  (13 13
      (:REWRITE CDR-OF-NAT-LIST-FIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV)))
(ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST)
(ABNF::PARSE-ANY-NAT-LIST-EQUIV-CONGRUENCE-ON-INPUT)
(ABNF::PARSE-EXACT
     (17 2
         (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
     (16 8 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
     (13 1 (:DEFINITION INTEGER-LISTP))
     (7 7 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (7 7
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
     (7 7
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
     (4 2
        (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
     (3 3 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE DEFAULT-CAR))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (2 1
        (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
     (1 1
        (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST)))
(ABNF::MAYBE-MSGP-OF-PARSE-EXACT.ERROR?
 (36 35 (:REWRITE DEFAULT-CAR))
 (22 22
     (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
 (20 20
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (17 17 (:REWRITE DEFAULT-CDR))
 (14 14
     (:REWRITE MSGP-WHEN-MEMBER-EQUAL-OF-MSG-LISTP))
 (12 12
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 2))
 (12 12
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 1))
 (7 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE DEFAULT-<-2))
 (2 2
    (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
 (2 2
    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2
    (:REWRITE CONS-OF-NFIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
 (2 2
    (:REWRITE CONS-OF-NAT-LIST-FIX-Y-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV)))
(ABNF::RETURN-TYPE-OF-PARSE-EXACT.TREE?
   (45 45
       (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
   (14 9 (:REWRITE DEFAULT-<-1))
   (9 9 (:REWRITE DEFAULT-<-2))
   (7 2
      (:REWRITE ABNF::TREEP-WHEN-MAYBE-TREEP))
   (4 4
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
   (3 3
      (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
   (3 3
      (:REWRITE CONS-OF-NFIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
   (3 3
      (:REWRITE CONS-OF-NAT-LIST-FIX-Y-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
   (2 2
      (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
   (2 2
      (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X)))
(ABNF::NAT-LISTP-OF-PARSE-EXACT.REST-INPUT
   (197 4 (:DEFINITION NAT-LISTP))
   (80 4 (:DEFINITION NATP))
   (68 8
       (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
   (65 4
       (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
   (52 4 (:DEFINITION INTEGER-LISTP))
   (49 49
       (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
   (37 19 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
   (28 28 (:TYPE-PRESCRIPTION INTEGER-LISTP))
   (20 4 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
   (17 17
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 2))
   (17 17
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 1))
   (16 8
       (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
   (12 10 (:REWRITE DEFAULT-<-1))
   (10 10 (:REWRITE DEFAULT-<-2))
   (8 8 (:REWRITE DEFAULT-CDR))
   (8 8 (:REWRITE DEFAULT-CAR))
   (8 4
      (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
   (4 4
      (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
   (4 4
      (:REWRITE CONS-OF-NFIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
   (4 4
      (:REWRITE CONS-OF-NAT-LIST-FIX-Y-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
   (2 2
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(ABNF::LEN-OF-PARSE-EXACT-LINEAR-<=
  (84 42 (:REWRITE DEFAULT-+-2))
  (57 57
      (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
  (42 42 (:REWRITE DEFAULT-+-1))
  (39 39 (:REWRITE DEFAULT-CDR))
  (36 36
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 2))
  (36 36
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 1))
  (32 18 (:REWRITE DEFAULT-<-1))
  (27 18 (:REWRITE DEFAULT-<-2))
  (4 4
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
  (3 3
     (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
  (3 3
     (:REWRITE CONS-OF-NFIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
  (3 3
     (:REWRITE CONS-OF-NAT-LIST-FIX-Y-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV)))
(ABNF::LEN-OF-PARSE-EXACT-LINEAR-<
  (84 12 (:DEFINITION LEN))
  (39 39
      (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
  (24 12 (:REWRITE DEFAULT-+-2))
  (17 10 (:REWRITE DEFAULT-<-1))
  (13 10 (:REWRITE DEFAULT-<-2))
  (12 12 (:REWRITE DEFAULT-CDR))
  (12 12 (:REWRITE DEFAULT-+-1))
  (12 12
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 2))
  (12 12
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 1))
  (3 3
     (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
  (3 3
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
  (3 3
     (:REWRITE CONS-OF-NFIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
  (3 3
     (:REWRITE CONS-OF-NAT-LIST-FIX-Y-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV)))
(ABNF::PARSE-EXACT-OF-NFIX-NAT)
(ABNF::PARSE-EXACT-OF-NFIX-NAT-NORMALIZE-CONST)
(ABNF::PARSE-EXACT-NAT-EQUIV-CONGRUENCE-ON-NAT)
(ABNF::PARSE-EXACT-OF-NAT-LIST-FIX-INPUT)
(ABNF::PARSE-EXACT-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST)
(ABNF::PARSE-EXACT-NAT-LIST-EQUIV-CONGRUENCE-ON-INPUT)
(ABNF::PARSE-EXACT-LIST-AUX
     (60 3 (:DEFINITION NATP))
     (44 22 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
     (39 3 (:DEFINITION INTEGER-LISTP))
     (25 25
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 2))
     (25 25
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                   . 1))
     (12 12 (:REWRITE DEFAULT-CAR))
     (12 6
         (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
     (10 10 (:REWRITE DEFAULT-CDR))
     (6 3
        (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
     (5 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:REWRITE DEFAULT-<-2))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
     (1 1
        (:REWRITE CAR-OF-NAT-LIST-FIX-X-NORMALIZE-CONST-UNDER-NAT-EQUIV))
     (1 1
        (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP)))
(ABNF::MAYBE-MSGP-OF-PARSE-EXACT-LIST-AUX.ERROR?
 (1514 29 (:REWRITE DEFAULT-<-1))
 (1194 30
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1185 30
       (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
 (1164 114
       (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (1155 15 (:DEFINITION ACL2-NUMBER-LISTP))
 (1044 60 (:DEFINITION RATIONAL-LISTP))
 (570 60
      (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (500 30 (:DEFINITION INTEGER-LISTP))
 (420 420 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (408 407 (:REWRITE DEFAULT-CAR))
 (372 90
      (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
 (344 344
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 2))
 (344 344
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 1))
 (276 132
      (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (256 256 (:REWRITE DEFAULT-CDR))
 (200 200 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (140 60
      (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (104
     104
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (99 99
     (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
 (98 98
     (:REWRITE MSGP-WHEN-MEMBER-EQUAL-OF-MSG-LISTP))
 (85 85
     (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
 (80 40
     (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (72 30
     (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
 (42 21
     (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
 (41 1
     (:REWRITE NAT-LIST-FIX-WHEN-NAT-LISTP))
 (35 1 (:DEFINITION NAT-LISTP))
 (29 29 (:REWRITE DEFAULT-<-2))
 (20 1 (:DEFINITION NATP))
 (7 7 (:TYPE-PRESCRIPTION NAT-LISTP))
 (6 2 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (3 3
    (:REWRITE CAR-OF-NAT-LIST-FIX-X-NORMALIZE-CONST-UNDER-NAT-EQUIV))
 (2 1 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (2 1
    (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP)))
(ABNF::NAT-LISTP-OF-PARSE-EXACT-LIST-AUX.REST-INPUT
     (1569 84 (:REWRITE DEFAULT-<-1))
     (1505 170
           (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
     (1215 85 (:DEFINITION INTEGER-LISTP))
     (1194 30
           (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1185 30
           (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
     (1164 114
           (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
     (1155 15 (:DEFINITION ACL2-NUMBER-LISTP))
     (1120 56 (:DEFINITION NATP))
     (1044 60 (:DEFINITION RATIONAL-LISTP))
     (491 243 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
     (444 444
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                    . 2))
     (444 444
          (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                    . 1))
     (372 90
          (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
     (360 170
          (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
     (320 320 (:REWRITE DEFAULT-CAR))
     (280 280 (:REWRITE DEFAULT-CDR))
     (276 132
          (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
     (190 95
          (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
     (91 91
         (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
     (84 84 (:REWRITE DEFAULT-<-2))
     (72 30
         (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
     (42 21
         (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
     (41 1
         (:REWRITE NAT-LIST-FIX-WHEN-NAT-LISTP))
     (3 3
        (:REWRITE CAR-OF-NAT-LIST-FIX-X-NORMALIZE-CONST-UNDER-NAT-EQUIV)))
(ABNF::PARSE-EXACT-LIST)
(ABNF::MAYBE-MSGP-OF-PARSE-EXACT-LIST.ERROR?
  (26 1 (:REWRITE MAYBE-MSGP-WHEN-MSGP))
  (21 1 (:DEFINITION MSGP))
  (14 1 (:DEFINITION CHARACTER-ALISTP))
  (4 4 (:TYPE-PRESCRIPTION CHARACTER-ALISTP))
  (4 4 (:REWRITE DEFAULT-CAR))
  (3 3 (:TYPE-PRESCRIPTION MSGP))
  (3 3
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 2))
  (3 3
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 1))
  (2 2
     (:REWRITE MSGP-WHEN-MEMBER-EQUAL-OF-MSG-LISTP))
  (2 2 (:REWRITE DEFAULT-CDR))
  (2 2
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
  (1 1
     (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST)))
(ABNF::RETURN-TYPE-OF-PARSE-EXACT-LIST.TREE?
     (7 2
        (:REWRITE ABNF::TREEP-WHEN-MAYBE-TREEP))
     (2 2
        (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
     (2 2
        (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
     (2 2
        (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST)))
(ABNF::NAT-LISTP-OF-PARSE-EXACT-LIST.REST-INPUT
     (39 1 (:DEFINITION NAT-LISTP))
     (20 1 (:DEFINITION NATP))
     (17 2
         (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
     (13 1 (:DEFINITION INTEGER-LISTP))
     (8 4 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
     (7 7 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (6 1
        (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
     (5 1 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
     (4 4
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
     (4 4
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
     (4 2
        (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
     (2 2
        (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-CAR))
     (2 1
        (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(ABNF::PARSE-IN-RANGE
     (17 2
         (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
     (16 8 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
     (13 10 (:REWRITE DEFAULT-<-1))
     (13 1 (:DEFINITION INTEGER-LISTP))
     (11 10 (:REWRITE DEFAULT-<-2))
     (7 7 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (7 7
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 2))
     (7 7
        (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                  . 1))
     (4 2
        (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
     (3 3 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE DEFAULT-CAR))
     (2 1
        (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
     (1 1
        (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST)))
(ABNF::MAYBE-MSGP-OF-PARSE-IN-RANGE.ERROR?
 (149 146 (:REWRITE DEFAULT-CAR))
 (92 92
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (89 63 (:REWRITE DEFAULT-<-1))
 (88 88
     (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
 (82 63 (:REWRITE DEFAULT-<-2))
 (68 68 (:REWRITE DEFAULT-CDR))
 (44 44
     (:REWRITE MSGP-WHEN-MEMBER-EQUAL-OF-MSG-LISTP))
 (30 30
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 2))
 (30 30
     (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
               . 1))
 (13 13
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4
    (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
 (4 4
    (:REWRITE CONS-OF-NFIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
 (4 4
    (:REWRITE CONS-OF-NAT-LIST-FIX-Y-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV)))
(ABNF::RETURN-TYPE-OF-PARSE-IN-RANGE.TREE?
   (146 146
        (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
   (128 89 (:REWRITE DEFAULT-<-1))
   (111 89 (:REWRITE DEFAULT-<-2))
   (25 25
       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
   (21 6
       (:REWRITE ABNF::TREEP-WHEN-MAYBE-TREEP))
   (7 7
      (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
   (7 7
      (:REWRITE CONS-OF-NFIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
   (7 7
      (:REWRITE CONS-OF-NAT-LIST-FIX-Y-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
   (6 6
      (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
   (6 6
      (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X)))
(ABNF::NAT-LISTP-OF-PARSE-IN-RANGE.REST-INPUT
  (566 10 (:DEFINITION NAT-LISTP))
  (236 10
       (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
  (200 10 (:DEFINITION NATP))
  (170 20
       (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
  (166 166
       (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
  (130 10 (:DEFINITION INTEGER-LISTP))
  (119 89 (:REWRITE DEFAULT-<-1))
  (118 89 (:REWRITE DEFAULT-<-2))
  (94 52 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
  (70 70 (:TYPE-PRESCRIPTION INTEGER-LISTP))
  (50 10
      (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
  (41 41
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 2))
  (41 41
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 1))
  (40 20
      (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
  (20 20 (:REWRITE DEFAULT-CDR))
  (20 20 (:REWRITE DEFAULT-CAR))
  (20 10
      (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
  (13 13
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
  (8 8
     (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
  (8 8
     (:REWRITE CONS-OF-NFIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
  (8 8
     (:REWRITE CONS-OF-NAT-LIST-FIX-Y-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV)))
(ABNF::LEN-OF-PARSE-IN-RANGE-LINEAR-<=
  (288 144 (:REWRITE DEFAULT-+-2))
  (188 188
       (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
  (188 119 (:REWRITE DEFAULT-<-1))
  (171 119 (:REWRITE DEFAULT-<-2))
  (144 144 (:REWRITE DEFAULT-+-1))
  (132 132 (:REWRITE DEFAULT-CDR))
  (120 120
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 2))
  (120 120
       (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                 . 1))
  (25 25
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
  (7 7
     (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
  (7 7
     (:REWRITE CONS-OF-NFIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
  (7 7
     (:REWRITE CONS-OF-NAT-LIST-FIX-Y-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV)))
(ABNF::LEN-OF-PARSE-IN-RANGE-LINEAR-<
  (252 36 (:DEFINITION LEN))
  (128 128
       (:REWRITE ABNF::PARSE-ANY-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST))
  (128 86 (:REWRITE DEFAULT-<-1))
  (117 86 (:REWRITE DEFAULT-<-2))
  (72 36 (:REWRITE DEFAULT-+-2))
  (36 36 (:REWRITE DEFAULT-CDR))
  (36 36 (:REWRITE DEFAULT-+-1))
  (36 36
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 2))
  (36 36
      (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP
                . 1))
  (19 19
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
  (7 7
     (:REWRITE ABNF::TREE-LEAFTERM-OF-NAT-LIST-FIX-GET-NORMALIZE-CONST))
  (7 7
     (:REWRITE CONS-OF-NFIX-X-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV))
  (7 7
     (:REWRITE CONS-OF-NAT-LIST-FIX-Y-NORMALIZE-CONST-UNDER-NAT-LIST-EQUIV)))
(ABNF::PARSE-IN-RANGE-OF-NFIX-MIN)
(ABNF::PARSE-IN-RANGE-OF-NFIX-MIN-NORMALIZE-CONST)
(ABNF::PARSE-IN-RANGE-NAT-EQUIV-CONGRUENCE-ON-MIN)
(ABNF::PARSE-IN-RANGE-OF-NFIX-MAX)
(ABNF::PARSE-IN-RANGE-OF-NFIX-MAX-NORMALIZE-CONST)
(ABNF::PARSE-IN-RANGE-NAT-EQUIV-CONGRUENCE-ON-MAX)
(ABNF::PARSE-IN-RANGE-OF-NAT-LIST-FIX-INPUT)
(ABNF::PARSE-IN-RANGE-OF-NAT-LIST-FIX-INPUT-NORMALIZE-CONST)
(ABNF::PARSE-IN-RANGE-NAT-LIST-EQUIV-CONGRUENCE-ON-INPUT)
