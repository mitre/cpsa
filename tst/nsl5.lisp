(herald nsl5 (bound 10))

(defprotocol nsl5 basic
  (defrole init
    (vars (a b c d e name)
      (na0 na1 na2 na3 nb0 nb1 nb2 nb3 nc0 nc1 nc2 nc3 nd0 nd1 nd2 nd3
        ne0 ne1 ne2 ne3 text))
    (trace
      (send
        (enc na0 a c d e (enc na1 a b d e (pubk c))
          (enc na2 a b c e (pubk d)) (enc na3 a b c d (pubk e))
          (pubk b)))
      (recv
        (enc na3 ne0 e b c d (enc na0 nb3 b c d e (pubk a))
          (enc na1 nc2 c b d e (pubk a)) (enc na2 nd1 d e b c (pubk a))
          (enc nb0 nc3 c d e a (pubk b)) (enc nb1 nd2 d c e a (pubk b))
          (enc nb2 ne1 e a c d (pubk b)) (enc nc0 nd3 d e a b (pubk c))
          (enc nc1 ne2 e a b d (pubk c)) (enc nd0 ne3 e a b c (pubk d))
          (pubk a)))
      (send
        (enc nb3 (enc nb0 nc3 c d e a (pubk b))
          (enc nb1 nd2 d c e a (pubk b)) (enc nb2 ne1 e a c d (pubk b))
          (enc nc0 nd3 d e a b (pubk c)) (enc nc1 ne2 e a b d (pubk c))
          (enc nc2 (pubk c)) (enc nd0 ne3 e a b c (pubk d))
          (enc nd1 (pubk d)) (enc ne0 (pubk e)) (pubk b))))
    (uniq-orig na0 na1 na2 na3))
  (defrole resp1
    (vars (a b c d e name)
      (na0 na1 na2 na3 nb0 nb1 nb2 nb3 nc0 nc1 nc2 nc3 nd0 nd1 nd2 nd3
        ne0 ne1 ne2 ne3 text))
    (trace
      (recv
        (enc na0 a c d e (enc na1 a b d e (pubk c))
          (enc na2 a b c e (pubk d)) (enc na3 a b c d (pubk e))
          (pubk b)))
      (send
        (enc nb0 b d e a (enc na1 a b d e (pubk c))
          (enc na2 a b c e (pubk d)) (enc nb1 b c e a (pubk d))
          (enc na3 a b c d (pubk e)) (enc nb2 b c d a (pubk e))
          (enc na0 nb3 b c d e (pubk a)) (pubk c)))
      (recv
        (enc nb3 (enc nb0 nc3 c d e a (pubk b))
          (enc nb1 nd2 d c e a (pubk b)) (enc nb2 ne1 e a c d (pubk b))
          (enc nc0 nd3 d e a b (pubk c)) (enc nc1 ne2 e a b d (pubk c))
          (enc nc2 (pubk c)) (enc nd0 ne3 e a b c (pubk d))
          (enc nd1 (pubk d)) (enc ne0 (pubk e)) (pubk b)))
      (send
        (enc nc3 (enc nc0 nd3 d e a b (pubk c))
          (enc nc1 ne2 e a b d (pubk c)) (enc nc2 (pubk c))
          (enc nd0 ne3 e a b c (pubk d)) (enc nd1 (pubk d))
          (enc nd2 (pubk d)) (enc ne0 (pubk e)) (enc ne1 (pubk e))
          (pubk c))))
    (uniq-orig nb0 nb1 nb2 nb3))
  (defrole resp2
    (vars (a b c d e name)
      (na0 na1 na2 na3 nb0 nb1 nb2 nb3 nc0 nc1 nc2 nc3 nd0 nd1 nd2 nd3
        ne0 ne1 ne2 ne3 text))
    (trace
      (recv
        (enc nb0 b d e a (enc na1 a b d e (pubk c))
          (enc na2 a b c e (pubk d)) (enc nb1 b c e a (pubk d))
          (enc na3 a b c d (pubk e)) (enc nb2 b c d a (pubk e))
          (enc na0 nb3 b c d e (pubk a)) (pubk c)))
      (send
        (enc nc0 c e a b (enc na2 a b c e (pubk d))
          (enc nb1 b c e a (pubk d)) (enc na3 a b c d (pubk e))
          (enc nb2 b c d a (pubk e)) (enc nc1 c d a b (pubk e))
          (enc na0 nb3 b c d e (pubk a)) (enc na1 nc2 c b d e (pubk a))
          (enc nb0 nc3 c d e a (pubk b)) (pubk d)))
      (recv
        (enc nc3 (enc nc0 nd3 d e a b (pubk c))
          (enc nc1 ne2 e a b d (pubk c)) (enc nc2 (pubk c))
          (enc nd0 ne3 e a b c (pubk d)) (enc nd1 (pubk d))
          (enc nd2 (pubk d)) (enc ne0 (pubk e)) (enc ne1 (pubk e))
          (pubk c)))
      (send
        (enc nd3 (enc nd0 ne3 e a b c (pubk d)) (enc nd1 (pubk d))
          (enc nd2 (pubk d)) (enc ne0 (pubk e)) (enc ne1 (pubk e))
          (enc ne2 (pubk e)) (pubk d))))
    (uniq-orig nc0 nc1 nc2 nc3))
  (defrole resp3
    (vars (a b c d e name)
      (na0 na1 na2 na3 nb0 nb1 nb2 nb3 nc0 nc1 nc2 nc3 nd0 nd1 nd2 nd3
        ne0 ne1 ne2 ne3 text))
    (trace
      (recv
        (enc nc0 c e a b (enc na2 a b c e (pubk d))
          (enc nb1 b c e a (pubk d)) (enc na3 a b c d (pubk e))
          (enc nb2 b c d a (pubk e)) (enc nc1 c d a b (pubk e))
          (enc na0 nb3 b c d e (pubk a)) (enc na1 nc2 c b d e (pubk a))
          (enc nb0 nc3 c d e a (pubk b)) (pubk d)))
      (send
        (enc nd0 d a b c (enc na3 a b c d (pubk e))
          (enc nb2 b c d a (pubk e)) (enc nc1 c d a b (pubk e))
          (enc na0 nb3 b c d e (pubk a)) (enc na1 nc2 c b d e (pubk a))
          (enc na2 nd1 d e b c (pubk a)) (enc nb0 nc3 c d e a (pubk b))
          (enc nb1 nd2 d c e a (pubk b)) (enc nc0 nd3 d e a b (pubk c))
          (pubk e)))
      (recv
        (enc nd3 (enc nd0 ne3 e a b c (pubk d)) (enc nd1 (pubk d))
          (enc nd2 (pubk d)) (enc ne0 (pubk e)) (enc ne1 (pubk e))
          (enc ne2 (pubk e)) (pubk d)))
      (send
        (enc ne3 (enc ne0 (pubk e)) (enc ne1 (pubk e))
          (enc ne2 (pubk e)) (pubk e))))
    (uniq-orig nd0 nd1 nd2 nd3))
  (defrole resp4
    (vars (a b c d e name)
      (na0 na1 na2 na3 nb0 nb1 nb2 nb3 nc0 nc1 nc2 nc3 nd0 nd1 nd2 nd3
        ne0 ne1 ne2 ne3 text))
    (trace
      (recv
        (enc nd0 d a b c (enc na3 a b c d (pubk e))
          (enc nb2 b c d a (pubk e)) (enc nc1 c d a b (pubk e))
          (enc na0 nb3 b c d e (pubk a)) (enc na1 nc2 c b d e (pubk a))
          (enc na2 nd1 d e b c (pubk a)) (enc nb0 nc3 c d e a (pubk b))
          (enc nb1 nd2 d c e a (pubk b)) (enc nc0 nd3 d e a b (pubk c))
          (pubk e)))
      (send
        (enc na3 ne0 e b c d (enc na0 nb3 b c d e (pubk a))
          (enc na1 nc2 c b d e (pubk a)) (enc na2 nd1 d e b c (pubk a))
          (enc nb0 nc3 c d e a (pubk b)) (enc nb1 nd2 d c e a (pubk b))
          (enc nb2 ne1 e a c d (pubk b)) (enc nc0 nd3 d e a b (pubk c))
          (enc nc1 ne2 e a b d (pubk c)) (enc nd0 ne3 e a b c (pubk d))
          (pubk a)))
      (recv
        (enc ne3 (enc ne0 (pubk e)) (enc ne1 (pubk e))
          (enc ne2 (pubk e)) (pubk e))))
    (uniq-orig ne0 ne1 ne2 ne3)))

(defskeleton nsl5 (vars (a b c d e name))
  (defstrand init 3 (a a) (b b) (c c) (d d) (e e))
  (non-orig (privk a) (privk b) (privk c) (privk d) (privk e)))

(defskeleton nsl5 (vars (a b c d e name))
  (defstrand resp1 4 (a a) (b b) (c c) (d d) (e e))
  (non-orig (privk a) (privk b) (privk c) (privk d) (privk e)))

(defskeleton nsl5 (vars (a b c d e name))
  (defstrand resp2 4 (a a) (b b) (c c) (d d) (e e))
  (non-orig (privk a) (privk b) (privk c) (privk d) (privk e)))

(defskeleton nsl5 (vars (a b c d e name))
  (defstrand resp3 4 (a a) (b b) (c c) (d d) (e e))
  (non-orig (privk a) (privk b) (privk c) (privk d) (privk e)))

(defskeleton nsl5 (vars (a b c d e name))
  (defstrand resp4 3 (a a) (b b) (c c) (d d) (e e))
  (non-orig (privk a) (privk b) (privk c) (privk d) (privk e)))
