(herald goalsvar)

;;; Section 1 --- Examples from CPSA and Formal Security Goals

;;; Needham-Schroeder from Section 10 of the CPSA Primer

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace
     (send (enc n1 a (pubk b)))
     (recv (enc n1 n2 (pubk a)))
     (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace
     (recv (enc n1 a (pubk b)))
     (send (enc n1 n2 (pubk a)))
     (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder with no role origination assumptions"))

(deflemma rule lemma1 ns
  (forall ((b name) (n1 text) (z0 strd))
    (implies
     (and 
      (strand init z0 3 (n1 n1) (b b))
      (non (privk b)) (uniq n1))
     (exists ((z1 strd))
	     (strand resp z1 2 (b b)))))
  (comment "Skeleton 1")
  (comment "Authentication goal: agreement on name b"))

(deflemma both lemma2 ns
  (forall ((b name) (n1 text) (z0 strd))
    (implies
     (and (strand init z0 3 (n1 n1) (b b))
      (non (privk b)) (uniq n1))
     (exists ((z1 strd))
        (and 
          (strand resp z1 2 (b b))
	      (prec z1 1 z0 2)))))
  (comment "Prec example. Skeleton 2"))

(deflemma goal lemma3 ns
  (forall ((a b name) (n2 text) (z0 strd))
    (implies
     (and (strand resp z0 3 (n2 n2) (a a) (b b))
      (non (privk a)) (uniq n2))
     (exists ((z1 strd))
      (strand init z1 2 (b b)))))
  (comment "Skeleton 3")
  (comment "Failed authentication goal: agreement on name b"))

(defgoal ns
  (forall ((a b name) (n2 text) (z0 strd))
    (implies
     (and (strand resp z0 3 (n2 n2) (a a) (b b))
      (non (privk a)) (uniq n2))
     (exists ((z1 strd))
      (strand init z1 2 (b b)))))
  (comment "Skeleton 4"))
