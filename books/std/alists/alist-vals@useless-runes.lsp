(ALIST-VALS)
(ALIST-VALS-WHEN-ATOM)
(ALIST-VALS-OF-CONS (17 17 (:REWRITE DEFAULT-CDR))
                    (15 15 (:REWRITE ALIST-VALS-WHEN-ATOM))
                    (10 10 (:REWRITE DEFAULT-CAR)))
(L0 (28 28 (:REWRITE DEFAULT-CDR))
    (25 25 (:REWRITE DEFAULT-CAR)))
(LIST-EQUIV-IMPLIES-EQUAL-ALIST-VALS-1
     (18 12 (:REWRITE ALIST-VALS-WHEN-ATOM))
     (12 12 (:REWRITE DEFAULT-CDR))
     (8 8 (:REWRITE DEFAULT-CAR)))
(TRUE-LISTP-OF-ALIST-VALS)
(ALIST-VALS-OF-HONS-ACONS (16 2 (:DEFINITION ALIST-VALS))
                          (7 7 (:REWRITE DEFAULT-CDR))
                          (6 6 (:REWRITE ALIST-VALS-WHEN-ATOM))
                          (4 4 (:REWRITE DEFAULT-CAR)))
(ALIST-VALS-OF-PAIRLIS$ (31 29 (:REWRITE DEFAULT-CDR))
                        (30 15 (:REWRITE ALIST-VALS-WHEN-ATOM))
                        (26 24 (:REWRITE DEFAULT-CAR))
                        (20 10 (:REWRITE DEFAULT-+-2))
                        (10 10 (:REWRITE DEFAULT-+-1)))
(LEN-OF-ALIST-VALS (32 16 (:REWRITE DEFAULT-+-2))
                   (27 25 (:REWRITE DEFAULT-CDR))
                   (19 19 (:REWRITE DEFAULT-CAR))
                   (16 16 (:REWRITE DEFAULT-+-1)))
(ALIST-VALS-OF-APPEND (59 58 (:REWRITE DEFAULT-CDR))
                      (48 47 (:REWRITE DEFAULT-CAR))
                      (30 30 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(ALIST-VALS-OF-REVAPPEND (83 58 (:REWRITE DEFAULT-CDR))
                         (72 47 (:REWRITE DEFAULT-CAR)))
(MEMBER-EQUAL-OF-CDR-WHEN-HONS-ASSOC-EQUAL
     (74 71 (:REWRITE DEFAULT-CAR))
     (43 36 (:REWRITE DEFAULT-CDR))
     (10 10 (:REWRITE ALIST-VALS-WHEN-ATOM)))
