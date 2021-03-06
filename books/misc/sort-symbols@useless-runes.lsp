(LEN-STRICT-MERGE-SYMBOL-<
     (515 228 (:REWRITE DEFAULT-+-2))
     (311 228 (:REWRITE DEFAULT-+-1))
     (220 193 (:REWRITE DEFAULT-CDR))
     (152 152 (:REWRITE DEFAULT-CAR))
     (134 37 (:REWRITE DEFAULT-<-1))
     (68 37 (:REWRITE DEFAULT-<-2))
     (56 28
         (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
     (28 28 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (28 28 (:TYPE-PRESCRIPTION REVAPPEND))
     (21 18 (:REWRITE SYMBOL-<-TRANSITIVE))
     (18 18 (:REWRITE SYMBOL-<-TRICHOTOMY))
     (17 17 (:REWRITE SYMBOL-<-ASYMMETRIC))
     (8 8 (:REWRITE CAR-CONS))
     (2 2 (:REWRITE CONS-CAR-CDR)))
(LEN-EVENS (76 38 (:REWRITE DEFAULT-+-2))
           (47 38 (:REWRITE DEFAULT-+-1))
           (17 17 (:REWRITE DEFAULT-CAR))
           (2 2 (:REWRITE CAR-CONS))
           (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(SYMBOL-LISTP-EVENS (24 21 (:REWRITE DEFAULT-CDR))
                    (20 17 (:REWRITE DEFAULT-CAR)))
(SYMBOL-LISTP-ODDS (6 6 (:REWRITE DEFAULT-CDR))
                   (4 4 (:REWRITE DEFAULT-CAR))
                   (4 1 (:DEFINITION EVENS)))
(SYMBOL-LISTP-STRICT-MERGE-SYMBOL-< (295 281 (:REWRITE DEFAULT-CAR))
                                    (143 129 (:REWRITE DEFAULT-CDR))
                                    (46 31 (:REWRITE SYMBOL-<-TRANSITIVE))
                                    (31 31 (:REWRITE SYMBOL-<-TRICHOTOMY))
                                    (26 26 (:REWRITE SYMBOL-<-ASYMMETRIC)))
(MEMBER-EQ-REVAPPEND-LEMMA (19 13 (:REWRITE DEFAULT-CAR))
                           (18 12 (:REWRITE DEFAULT-CDR)))
(MEMBER-EQ-REVAPPEND (61 52 (:REWRITE DEFAULT-CAR))
                     (51 42 (:REWRITE DEFAULT-CDR)))
(MEMBER-EQ-STRICT-MERGE-SYMBOL-< (466 466 (:REWRITE DEFAULT-CAR))
                                 (253 253 (:REWRITE DEFAULT-CDR))
                                 (148 36 (:DEFINITION REVAPPEND))
                                 (55 43 (:REWRITE SYMBOL-<-TRANSITIVE))
                                 (43 43 (:REWRITE SYMBOL-<-TRICHOTOMY))
                                 (39 39 (:REWRITE SYMBOL-<-ASYMMETRIC))
                                 (4 4 (:REWRITE CONS-CAR-CDR)))
(MEMBER-EQ-EVENS (204 188 (:REWRITE DEFAULT-CAR)))
(MEMBER-EQ-STRICT-MERGE-SORT-SYMBOL-<
     (396 22 (:DEFINITION STRICT-MERGE-SYMBOL-<))
     (281 281 (:REWRITE DEFAULT-CAR))
     (44 44 (:DEFINITION REVAPPEND))
     (22 22 (:TYPE-PRESCRIPTION SYMBOL-<))
     (22 22 (:REWRITE SYMBOL-<-TRICHOTOMY))
     (22 22 (:REWRITE SYMBOL-<-TRANSITIVE))
     (22 22 (:REWRITE SYMBOL-<-ASYMMETRIC))
     (4 4 (:REWRITE CDR-CONS))
     (4 4 (:REWRITE CAR-CONS)))
(MEMBER-EQ-SORT-SYMBOL-LISTP (86 86 (:REWRITE DEFAULT-CAR))
                             (30 1
                                 (:DEFINITION STRICT-MERGE-SORT-SYMBOL-<))
                             (18 1 (:DEFINITION STRICT-MERGE-SYMBOL-<))
                             (16 16 (:REWRITE SYMBOL-<-TRICHOTOMY))
                             (16 16 (:REWRITE SYMBOL-<-TRANSITIVE))
                             (16 16 (:REWRITE SYMBOL-<-ASYMMETRIC))
                             (6 1 (:DEFINITION ODDS))
                             (2 2 (:DEFINITION REVAPPEND)))
(STRICT-SYMBOL->-SORTEDP (58 28 (:REWRITE DEFAULT-+-2))
                         (39 28 (:REWRITE DEFAULT-+-1))
                         (24 6 (:REWRITE COMMUTATIVITY-OF-+))
                         (24 6 (:DEFINITION INTEGER-ABS))
                         (24 3 (:DEFINITION LENGTH))
                         (15 3 (:DEFINITION LEN))
                         (14 14 (:REWRITE DEFAULT-CDR))
                         (12 12 (:REWRITE DEFAULT-CAR))
                         (9 7 (:REWRITE DEFAULT-<-2))
                         (8 8 (:REWRITE FOLD-CONSTS-IN-+))
                         (8 7 (:REWRITE DEFAULT-<-1))
                         (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
                         (3 3 (:TYPE-PRESCRIPTION LEN))
                         (3 3 (:REWRITE DEFAULT-REALPART))
                         (3 3 (:REWRITE DEFAULT-NUMERATOR))
                         (3 3 (:REWRITE DEFAULT-IMAGPART))
                         (3 3 (:REWRITE DEFAULT-DENOMINATOR))
                         (3 3 (:REWRITE DEFAULT-COERCE-2))
                         (3 3 (:REWRITE DEFAULT-COERCE-1))
                         (1 1 (:REWRITE SYMBOL-<-TRICHOTOMY))
                         (1 1 (:REWRITE SYMBOL-<-TRANSITIVE))
                         (1 1 (:REWRITE SYMBOL-<-ASYMMETRIC)))
(SORTED-LISTS-SYMBOL->)
(STRICT-SYMBOL-<-REVAPPEND (291 225 (:REWRITE DEFAULT-CDR))
                           (149 92 (:REWRITE SYMBOL-<-TRICHOTOMY))
                           (139 83 (:REWRITE SYMBOL-<-ASYMMETRIC))
                           (94 91 (:REWRITE SYMBOL-<-TRANSITIVE)))
(STRICT-SYMBOL-<-SORTEDP-STRICT-MERGE-SYMBOL-<
     (5542 5461 (:REWRITE DEFAULT-CAR))
     (4074 3897 (:REWRITE DEFAULT-CDR))
     (314 260
          (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
     (260 260 (:TYPE-PRESCRIPTION REVAPPEND))
     (54 54 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(STRICT-SYMBOL-<-SORTEDP-STRICT-MERGE-SORT-SYMBOL-<
     (234 13 (:DEFINITION STRICT-MERGE-SYMBOL-<))
     (223 187 (:REWRITE DEFAULT-CDR))
     (158 158 (:REWRITE DEFAULT-CAR))
     (108 24 (:DEFINITION EVENS))
     (62 62 (:TYPE-PRESCRIPTION EVENS))
     (27 27 (:TYPE-PRESCRIPTION SYMBOL-<))
     (26 26 (:DEFINITION REVAPPEND))
     (25 25 (:REWRITE SYMBOL-<-TRICHOTOMY))
     (25 25 (:REWRITE SYMBOL-<-TRANSITIVE))
     (23 23 (:REWRITE SYMBOL-<-ASYMMETRIC))
     (12 2 (:REWRITE SYMBOL-LISTP-ODDS)))
(STRICT-SYMBOL-<-SORTEDP-SORT-SYMBOL-LISTP
     (30 1
         (:DEFINITION STRICT-MERGE-SORT-SYMBOL-<))
     (23 2 (:DEFINITION STRICT-SYMBOL-<-SORTEDP))
     (18 1 (:DEFINITION STRICT-MERGE-SYMBOL-<))
     (17 17 (:REWRITE DEFAULT-CDR))
     (14 14 (:REWRITE DEFAULT-CAR))
     (8 2 (:DEFINITION EVENS))
     (6 1 (:DEFINITION ODDS))
     (3 3 (:TYPE-PRESCRIPTION SYMBOL-<))
     (3 3 (:REWRITE SYMBOL-<-TRICHOTOMY))
     (3 3 (:REWRITE SYMBOL-<-TRANSITIVE))
     (3 3 (:REWRITE SYMBOL-<-ASYMMETRIC))
     (3 1 (:DEFINITION SYMBOL-LISTP))
     (2 2 (:DEFINITION REVAPPEND)))
