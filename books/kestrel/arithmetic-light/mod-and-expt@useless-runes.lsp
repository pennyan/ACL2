(MOD-EXPT-SPLIT
     (9765 110
           (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (3261 48 (:REWRITE MOD-WHEN-<))
     (3045 3045 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (2078 30 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (1832 443 (:REWRITE DEFAULT-*-2))
     (1623 53 (:REWRITE <-OF-*-OF-/-ARG1-ARG2))
     (1498 53 (:REWRITE MOD-WHEN-MULTIPLE))
     (1221 201 (:REWRITE INTEGERP-OF-*))
     (1035 443 (:REWRITE DEFAULT-*-1))
     (877 244 (:REWRITE DEFAULT-<-2))
     (745 30
          (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (592 12 (:REWRITE <-OF-*-AND-0))
     (573 48 (:REWRITE MOD-OF-1-WHEN-INTEGERP))
     (310 244 (:REWRITE DEFAULT-<-1))
     (267 31 (:REWRITE DEFAULT-UNARY-/))
     (241 53
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (221 53
          (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (221 53
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (220 220 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (220 220
          (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (220 220 (:LINEAR <-OF-*-AND-*))
     (145 145 (:REWRITE DEFAULT-+-2))
     (145 145 (:REWRITE DEFAULT-+-1))
     (110 110
          (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (110 110
          (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (110 110
          (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (110 110
          (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (100 100
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (90 1 (:REWRITE <-OF-*-OF-/-ARG1-ARG1))
     (73 53
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (57 57
         (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (56 56 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (56 56 (:LINEAR EXPT-BOUND-LINEAR))
     (51 51
         (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG2))
     (51 51
         (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG1))
     (36 3 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (27 27 (:REWRITE *-OF-0))
     (18 3 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
     (6 6 (:REWRITE EQUAL-OF-*-AND-CONSTANT)))
(MOD-EXPT-SPLIT2
     (1294 15 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (603 603
          (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (601 601 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (566 13
          (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (469 8 (:REWRITE MOD-WHEN-<))
     (417 13 (:REWRITE MOD-WHEN-MULTIPLE))
     (404 87 (:REWRITE DEFAULT-*-2))
     (318 6 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (245 41 (:REWRITE INTEGERP-OF-*))
     (242 86
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (187 87 (:REWRITE DEFAULT-*-1))
     (178 19 (:REWRITE COMMUTATIVITY-OF-*))
     (153 5 (:REWRITE <-OF-*-OF-/-ARG1-ARG2))
     (149 6
          (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (144 4 (:REWRITE <-OF-*-AND-0))
     (135 15 (:REWRITE DEFAULT-UNARY-/))
     (129 40 (:REWRITE DEFAULT-<-2))
     (100 40 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
     (99 8 (:REWRITE MOD-OF-1-WHEN-INTEGERP))
     (65 13
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (60 40 (:REWRITE DEFAULT-<-1))
     (48 2 (:DEFINITION EXPT))
     (45 13
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (45 13
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (36 6 (:REWRITE UNICITY-OF-1))
     (33 13
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (30 30 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (30 30
         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (30 30 (:LINEAR <-OF-*-AND-*))
     (18 3 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
     (15 15 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (15 15 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (15 15 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (15 15 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (13 13
         (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (12 4 (:REWRITE COMMUTATIVITY-OF-+))
     (11 11
         (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG2))
     (11 11
         (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG1))
     (9 9 (:REWRITE DEFAULT-+-2))
     (9 9 (:REWRITE DEFAULT-+-1))
     (8 8 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (8 8 (:LINEAR EXPT-BOUND-LINEAR))
     (4 4
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (3 3 (:REWRITE *-OF-0))
     (2 2 (:REWRITE ZIP-OPEN)))
(MOD-OF-EXPT-TWICE
     (1640 56
           (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (1528 56 (:REWRITE MOD-WHEN-MULTIPLE))
     (513 101 (:REWRITE DEFAULT-UNARY-/))
     (503 137 (:REWRITE DEFAULT-*-2))
     (484 36 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (395 137 (:REWRITE DEFAULT-*-1))
     (340 36 (:REWRITE COMMUTATIVITY-OF-*))
     (297 101 (:REWRITE INTEGERP-OF-*))
     (265 265
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (262 262 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (224 56
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (142 20
          (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (137 45
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (125 45
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (91 54 (:REWRITE DEFAULT-<-1))
     (64 54 (:REWRITE DEFAULT-<-2))
     (56 56
         (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (51 11
         (:REWRITE INTEGERP-OF-*-OF-EXPT2-AND-/-OF-EXPT2))
     (34 8 (:REWRITE INTEGERP-OF-MOD))
     (16 16
         (:REWRITE MOD-OF-MOD-WHEN-MULTIPLE-SAFE))
     (14 14
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 4 (:REWRITE RATIONALP-OF-MOD)))
(MOD-OF-EXPT-AND-EXPT
     (386 11
          (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (298 11 (:REWRITE MOD-WHEN-MULTIPLE))
     (110 22 (:REWRITE INTEGERP-OF-*))
     (110 22 (:REWRITE DEFAULT-UNARY-/))
     (90 22
         (:REWRITE INTEGERP-OF-*-OF-EXPT2-AND-/-OF-EXPT2))
     (66 22 (:REWRITE DEFAULT-*-2))
     (66 22 (:REWRITE DEFAULT-*-1))
     (55 11
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (48 40 (:REWRITE DEFAULT-<-2))
     (48 40 (:REWRITE DEFAULT-<-1))
     (33 11
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (33 11
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (33 11
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (11 11
         (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (10 10 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (9 3 (:REWRITE DEFAULT-+-2))
     (3 3 (:REWRITE DEFAULT-+-1)))
(MOD-OF-MOD-OF-EXPT-AND-2
     (375 375
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (375 375
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (373 373
          (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (284 12
          (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (276 12 (:REWRITE MOD-WHEN-MULTIPLE))
     (200 12 (:REWRITE MOD-WHEN-<))
     (120 12 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (112 16 (:REWRITE COMMUTATIVITY-OF-*))
     (96 36 (:REWRITE DEFAULT-*-2))
     (88 36 (:REWRITE DEFAULT-*-1))
     (88 12
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (88 12
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (40 12
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (40 12 (:REWRITE DEFAULT-<-1))
     (38 6 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (38 6 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (34 6
         (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (30 6 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
     (24 24
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (20 4 (:REWRITE DEFAULT-UNARY-/))
     (17 1 (:REWRITE EQUAL-OF-MOD-SAME-ARG1))
     (16 16 (:REWRITE INTEGERP-OF-*))
     (16 12
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (16 12 (:REWRITE DEFAULT-<-2))
     (13 13 (:REWRITE RATIONALP-OF-MOD))
     (12 12
         (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (12 4 (:REWRITE UNICITY-OF-1))
     (10 4
         (:REWRITE MOD-OF-MOD-WHEN-MULTIPLE-SAFE))
     (8 4 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (8 4 (:DEFINITION FIX))
     (8 2 (:REWRITE INTEGERP-OF-MOD-OF-1))
     (7 7 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (4 4 (:REWRITE MOD-OF-1-WHEN-INTEGERP))
     (4 4 (:LINEAR EXPT-BOUND-LINEAR)))
(INTEGERP-OF-HALF-OF-MOD-OF-EXPT
     (101 9
          (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (93 9 (:REWRITE MOD-WHEN-MULTIPLE))
     (39 9 (:REWRITE MOD-WHEN-<))
     (36 2
         (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (30 2 (:LINEAR MOD-BOUND-LINEAR-ARG2))
     (21 4 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (17 8 (:REWRITE DEFAULT-*-2))
     (12 6 (:REWRITE INTEGERP-OF-*))
     (11 9
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (11 9
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (11 9 (:REWRITE DEFAULT-<-2))
     (10 2 (:REWRITE DEFAULT-UNARY-/))
     (9 9
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (9 9
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (9 9
        (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (9 9 (:REWRITE DEFAULT-<-1))
     (8 8 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
     (8 8 (:REWRITE DEFAULT-*-1))
     (6 2 (:REWRITE COMMUTATIVITY-OF-*))
     (6 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (6 2 (:LINEAR EXPT-BOUND-LINEAR))
     (2 2
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (2 2 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (2 2 (:LINEAR EXPT-BOUND-LINEAR-WEAK)))
(MOD-OF-HALF-AND-EXPT-OF-ONE-LESS
     (1033 1033 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (1002 14 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (680 6 (:REWRITE MOD-WHEN-<))
     (669 163 (:REWRITE DEFAULT-*-2))
     (429 10
          (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (393 10 (:REWRITE MOD-WHEN-MULTIPLE))
     (330 5 (:REWRITE <-OF-*-OF-/-ARG1-ARG1))
     (304 8 (:REWRITE <-OF-*-OF-/-ARG1-ARG2))
     (292 27 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (287 89
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (277 33 (:REWRITE DEFAULT-UNARY-/))
     (259 163 (:REWRITE DEFAULT-*-1))
     (191 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (152 58 (:REWRITE DEFAULT-<-2))
     (150 48 (:REWRITE INTEGERP-OF-*))
     (120 6 (:REWRITE MOD-OF-1-WHEN-INTEGERP))
     (83 83 (:REWRITE DEFAULT-+-2))
     (83 83 (:REWRITE DEFAULT-+-1))
     (73 4
         (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (58 58 (:REWRITE DEFAULT-<-1))
     (50 10
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (34 10
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (34 10
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (28 28 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (28 28
         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (28 28 (:LINEAR <-OF-*-AND-*))
     (26 10
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (14 14 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (14 14 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (14 14 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (14 14 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (10 10
         (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (8 8
        (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG2))
     (8 8
        (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG1))
     (8 8 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (8 8 (:LINEAR EXPT-BOUND-LINEAR))
     (7 7
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (6 1 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
     (2 2 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
     (2 2 (:REWRITE *-OF-0)))
(MOD-OF-HALF-AND-EXPT-OF-ONE-LESS-ALT
     (451 6 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (372 4 (:REWRITE MOD-WHEN-<))
     (357 357
          (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (355 355 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (269 62 (:REWRITE DEFAULT-*-2))
     (261 7 (:REWRITE MOD-WHEN-MULTIPLE))
     (207 5 (:REWRITE <-OF-*-OF-/-ARG1-ARG2))
     (146 62 (:REWRITE DEFAULT-*-1))
     (125 53
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (90 10 (:REWRITE DEFAULT-UNARY-/))
     (81 21 (:REWRITE INTEGERP-OF-*))
     (76 3 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (72 12 (:REWRITE UNICITY-OF-1))
     (64 17 (:REWRITE DEFAULT-<-2))
     (56 4 (:REWRITE MOD-OF-1-WHEN-INTEGERP))
     (48 2 (:DEFINITION EXPT))
     (47 3
         (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
     (35 7
         (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (23 7
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (23 7
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (21 21 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
     (19 7
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (17 17 (:REWRITE DEFAULT-<-1))
     (12 12 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (12 12
         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (12 12 (:LINEAR <-OF-*-AND-*))
     (12 4 (:REWRITE COMMUTATIVITY-OF-+))
     (8 8
        (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (8 8 (:REWRITE DEFAULT-+-2))
     (8 8 (:REWRITE DEFAULT-+-1))
     (7 7
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (6 1 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
     (5 5
        (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG2))
     (5 5
        (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG1))
     (4 4 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (4 4 (:LINEAR EXPT-BOUND-LINEAR))
     (4 1 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
     (3 1 (:REWRITE <-OF-*-OF-/-ARG1-ARG1))
     (2 2 (:REWRITE ZIP-OPEN))
     (1 1 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
     (1 1 (:REWRITE *-OF-0)))
(INTEGERP-OF-HALF-WHEN-MULT-OF-EXPT
     (47 3 (:REWRITE MOD-WHEN-<))
     (35 7 (:REWRITE DEFAULT-UNARY-/))
     (33 3 (:REWRITE MOD-WHEN-MULTIPLE))
     (33 3
         (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (29 11 (:REWRITE DEFAULT-*-2))
     (21 21 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (13 11 (:REWRITE DEFAULT-*-1))
     (10 4 (:REWRITE DEFAULT-<-2))
     (9 3
        (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (9 3
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (6 6
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (5 3 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (3 3
        (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (3 3
        (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (3 3
        (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (3 3 (:REWRITE DEFAULT-+-1))
     (3 1 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (1 1 (:REWRITE *-OF-*-COMBINE-CONSTANTS)))
(MOD-OF-*-OF-EXPT-AND-EXPT-BOUND-HELPER
     (26319 26
            (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
     (10342 43
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (9754 9754 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (9754 9754
           (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (8733 69 (:REWRITE FLOOR-WHEN-<))
     (5457 75 (:REWRITE CANCEL-FLOOR-+))
     (5409 75 (:REWRITE FLOOR-ZERO . 3))
     (3196 466 (:REWRITE DEFAULT-*-2))
     (2854 238 (:REWRITE DEFAULT-UNARY-/))
     (2557 151 (:REWRITE INTEGERP-OF-*))
     (2283 15 (:REWRITE MOD-WHEN-<))
     (2049 677 (:REWRITE DEFAULT-<-2))
     (2033 593 (:REWRITE DEFAULT-+-2))
     (1599 15 (:REWRITE MOD-X-Y-=-X . 3))
     (1433 1433
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1433 1433
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1407 15 (:REWRITE CANCEL-MOD-+))
     (1326 15
           (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (1263 75 (:REWRITE FLOOR-ZERO . 4))
     (1227 15 (:REWRITE MOD-ZERO . 2))
     (1171 1015
           (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (1006 1006 (:REWRITE |(< (- x) (- y))|))
     (993 75 (:REWRITE FLOOR-ZERO . 2))
     (939 15 (:REWRITE MOD-WHEN-MULTIPLE))
     (899 677 (:REWRITE DEFAULT-<-1))
     (836 593 (:REWRITE DEFAULT-+-1))
     (764 6 (:REWRITE |(< d (+ c x y))|))
     (759 69
          (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
     (755 197 (:REWRITE |(< d (+ c x))|))
     (699 273 (:REWRITE DEFAULT-UNARY-MINUS))
     (664 466 (:REWRITE DEFAULT-*-1))
     (659 659 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (659 659 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (659 659
          (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
     (659 659
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (659 659
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (659 659
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
     (659 659
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
     (659 659
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
     (659 659
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (659 659
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (593 593
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (577 97 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (577 97
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (543 75 (:REWRITE FLOOR-COMPLETION))
     (543 75 (:REWRITE FLOOR-CANCEL-*-WEAK))
     (530 7 (:LINEAR FLOOR-BOUNDS-3))
     (530 7 (:LINEAR FLOOR-BOUNDS-2))
     (513 19
          (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
     (493 43
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (489 75 (:REWRITE FLOOR-MINUS-WEAK))
     (489 75 (:REWRITE FLOOR-MINUS-2))
     (436 436 (:REWRITE DEFAULT-EXPT-2))
     (436 436 (:REWRITE DEFAULT-EXPT-1))
     (436 436 (:REWRITE |(expt x (- n))|))
     (436 436 (:REWRITE |(expt 2^i n)|))
     (436 436 (:REWRITE |(expt 1/c n)|))
     (436 436 (:REWRITE |(expt (- x) n)|))
     (423 15 (:REWRITE MOD-X-Y-=-X . 4))
     (387 4 (:REWRITE <-OF-*-OF-/-ARG2-ARG2))
     (363 15 (:REWRITE MOD-ZERO . 3))
     (347 271 (:REWRITE |(< (+ c x) d)|))
     (339 312
          (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
     (339 312 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (312 312
          (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (312 312
          (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (290 290 (:REWRITE INTEGERP-MINUS-X))
     (290 290 (:META META-INTEGERP-CORRECT))
     (259 34 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (252 18 (:REWRITE |(collect-* y x)|))
     (238 238
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (203 95
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (173 173 (:REWRITE |(< 0 (- x))|))
     (162 162
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (156 156 (:LINEAR EXPT->-1-TWO))
     (156 156 (:LINEAR EXPT-<-1-ONE))
     (151 151 (:REWRITE |(integerp (* c x))|))
     (138 30 (:REWRITE MOD-COMPLETION))
     (126 1 (:LINEAR MOD-BOUNDS-3))
     (123 15 (:REWRITE MOD-X-Y-=-X . 2))
     (123 15
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (123 15 (:REWRITE MOD-NEG))
     (123 15 (:REWRITE MOD-MINUS-2))
     (123 15 (:REWRITE MOD-CANCEL-*))
     (118 118 (:REWRITE |(< (- x) 0)|))
     (114 6 (:REWRITE |(equal (* x y) 0)|))
     (105 15 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (105 15 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (105 15
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (101 14 (:REWRITE |(< (+ d x) (+ c y))|))
     (97 97
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (97 97 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (97 97
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (97 97
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (90 14 (:REWRITE |(< (+ c x) (+ d y))|))
     (69 69
         (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
     (69 69
         (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
     (69 69
         (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
     (69 69
         (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
     (69 69 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (45 45 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (43 43 (:REWRITE |(equal (- x) (- y))|))
     (34 34 (:REWRITE |(equal (- x) 0)|))
     (33 15
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (33 15
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (32 2 (:LINEAR MOD-BOUNDS-2))
     (25 25
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (25 25
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (25 25 (:REWRITE |(* c (* d x))|))
     (25 1 (:REWRITE |(* x (expt x n))|))
     (21 21 (:REWRITE FOLD-CONSTS-IN-+))
     (15 15
         (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (13 13 (:REWRITE |(* (- x) y)|))
     (10 10 (:REWRITE *-OF---ARG1))
     (9 9 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
     (9 9 (:REWRITE |(equal (+ c x) d)|))
     (6 6
        (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG2))
     (6 6
        (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG1))
     (6 1 (:REWRITE BUBBLE-DOWN-+-BUBBLE-DOWN))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (4 4
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (4 4
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (4 4 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
     (2 2
        (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (2 2 (:REWRITE |(< (+ c x y) d)|))
     (2 1 (:REWRITE |(+ (* c x) (* d x))|))
     (1 1 (:REWRITE <-OF-*-AND-*)))
(MOD-OF-*-OF-EXPT-AND-EXPT-BOUND
     (2214 114
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2176 16 (:REWRITE MOD-X-Y-=-X . 3))
     (1915 16 (:REWRITE CANCEL-MOD-+))
     (1541 16 (:REWRITE MOD-ZERO . 3))
     (1287 15 (:REWRITE MOD-WHEN-<))
     (1124 4 (:REWRITE |(equal (* x y) 0)|))
     (823 171 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (823 171
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (819 16
          (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
     (811 16 (:REWRITE MOD-ZERO . 2))
     (795 795 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (795 795
          (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (770 35 (:REWRITE INTEGERP-OF-*))
     (704 19 (:REWRITE |(* (* x y) z)|))
     (675 16 (:REWRITE MOD-X-Y-=-X . 4))
     (575 16 (:REWRITE MOD-WHEN-MULTIPLE))
     (514 71
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (511 43 (:REWRITE DEFAULT-UNARY-/))
     (501 6 (:REWRITE <-OF-*-AND-0))
     (462 23 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
     (451 48 (:REWRITE DEFAULT-*-2))
     (427 427
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (427 427
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (427 427
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (297 11
          (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
     (290 89 (:REWRITE SIMPLIFY-SUMS-<))
     (280 23
          (:REWRITE |(* (expt x m) (/ (expt x n)))|))
     (255 19 (:REWRITE BUBBLE-DOWN-*-MATCH-1))
     (192 73 (:REWRITE DEFAULT-<-2))
     (192 4 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
     (181 48 (:REWRITE DEFAULT-*-1))
     (172 3 (:LINEAR MOD-BOUNDS-3))
     (171 171
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (171 171
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (171 171
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (171 171
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (171 32 (:REWRITE MOD-COMPLETION))
     (155 16
          (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
     (155 16 (:REWRITE MOD-CANCEL-*))
     (148 148
          (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
     (143 16 (:REWRITE MOD-NEG))
     (117 3 (:LINEAR MOD-BOUND-LINEAR-ARG1))
     (114 114
          (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (114 114 (:REWRITE |(< (- x) (- y))|))
     (113 10 (:LINEAR EXPT-X->=-X))
     (113 10 (:LINEAR EXPT-X->-X))
     (112 16 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
     (112 16 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
     (112 16
          (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
     (110 73 (:REWRITE DEFAULT-<-1))
     (100 16 (:REWRITE MOD-MINUS-2))
     (98 4 (:REWRITE |(* y (* x z))|))
     (94 10 (:LINEAR EXPT-<-1-TWO))
     (92 92 (:REWRITE DEFAULT-EXPT-2))
     (92 92 (:REWRITE DEFAULT-EXPT-1))
     (92 92 (:REWRITE |(expt x (- n))|))
     (92 92 (:REWRITE |(expt 2^i n)|))
     (92 92 (:REWRITE |(expt 1/c n)|))
     (92 92 (:REWRITE |(expt (- x) n)|))
     (88 16 (:REWRITE MOD-X-Y-=-X . 2))
     (84 6 (:LINEAR MOD-BOUNDS-2))
     (72 32 (:REWRITE DEFAULT-+-2))
     (70 70
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (66 11 (:REWRITE |(+ y (+ x z))|))
     (59 16
         (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
     (59 16
         (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
     (56 4 (:REWRITE |(collect-* y x)|))
     (52 52 (:REWRITE REDUCE-INTEGERP-+))
     (52 52 (:REWRITE INTEGERP-MINUS-X))
     (52 52 (:META META-INTEGERP-CORRECT))
     (46 46 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
     (46 46
         (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
     (46 46 (:LINEAR <-OF-*-AND-*))
     (43 43
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (43 43 (:REWRITE |(< (- x) 0)|))
     (38 32 (:REWRITE DEFAULT-+-1))
     (35 35 (:REWRITE |(integerp (* c x))|))
     (34 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (34 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (34 9
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (32 32
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (32 1 (:REWRITE |(* a (/ a) b)|))
     (29 29
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (27 24 (:REWRITE DEFAULT-UNARY-MINUS))
     (23 23 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
     (23 23 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
     (23 23 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
     (23 23 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
     (22 11 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (21 21
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (21 21 (:REWRITE |(< 0 (- x))|))
     (21 21 (:REWRITE |(< (+ c x) d)|))
     (21 21 (:REWRITE |(+ c (+ d x))|))
     (21 3 (:REWRITE |(* a (/ a))|))
     (20 20
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (20 20
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (16 16
         (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
     (10 10 (:REWRITE <-OF-0-AND-EXPT))
     (10 10 (:LINEAR EXPT->-1-TWO))
     (10 10 (:LINEAR EXPT-<-1-ONE))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (9 9 (:REWRITE |(equal (- x) 0)|))
     (9 9 (:REWRITE |(equal (- x) (- y))|))
     (9 9 (:REWRITE |(* c (* d x))|))
     (8 8 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
     (8 8
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
     (8 8
        (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
     (7 7 (:REWRITE |(< d (+ c x))|))
     (7 1 (:REWRITE MOD-+-CANCEL-0-WEAK))
     (6 6
        (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG2))
     (6 6
        (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG1))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:REWRITE |(* 1 x)|))
     (1 1 (:REWRITE MOD-ZERO . 1))
     (1 1 (:REWRITE MOD-NEGATIVE . 3))
     (1 1 (:REWRITE MOD-NEGATIVE . 2)))
