(EQUAL-LEN-CONST (9 5 (:REWRITE DEFAULT-+-2))
                 (5 5 (:REWRITE DEFAULT-CDR))
                 (5 5 (:REWRITE DEFAULT-+-1))
                 (1 1 (:REWRITE DEFAULT-<-2))
                 (1 1 (:REWRITE DEFAULT-<-1)))
(GTEQ-LEN-CONST (10 5 (:REWRITE DEFAULT-+-2))
                (6 4 (:REWRITE DEFAULT-<-1))
                (5 5 (:REWRITE DEFAULT-CDR))
                (5 5 (:REWRITE DEFAULT-+-1))
                (5 4 (:REWRITE DEFAULT-<-2))
                (4 4
                   (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(LEMMA (16 8 (:REWRITE DEFAULT-+-2))
       (8 8 (:REWRITE DEFAULT-CDR))
       (8 8 (:REWRITE DEFAULT-+-1))
       (7 4 (:REWRITE DEFAULT-<-2))
       (5 4 (:REWRITE DEFAULT-<-1))
       (3 3
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(GT-LEN-CONST (34 23 (:REWRITE DEFAULT-<-2))
              (23 23 (:REWRITE DEFAULT-CDR))
              (22 22 (:REWRITE DEFAULT-+-1))
              (14 14
                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
