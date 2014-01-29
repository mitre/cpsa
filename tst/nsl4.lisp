(defprotocol nsl4 basic
  (defrole init
    (vars (a b c d name)
      (na0 na1 na2 nb0 nb1 nb2 nc0 nc1 nc2 nd0 nd1 nd2 text))
    (trace
      (send
        (enc na0 a c d (enc na1 a b d (pubk c)) (enc na2 a b c (pubk d))
          (pubk b)))
      (recv
        (enc na2 nd0 d b c (enc na0 nb2 b c d (pubk a))
          (enc na1 nc1 c b d (pubk a)) (enc nb0 nc2 c d a (pubk b))
          (enc nb1 nd1 d a c (pubk b)) (enc nc0 nd2 d a b (pubk c))
          (pubk a)))
      (send
        (enc nb2 (enc nb0 nc2 c d a (pubk b))
          (enc nb1 nd1 d a c (pubk b)) (enc nc0 nd2 d a b (pubk c))
          (enc nc1 (pubk c)) (enc nd0 (pubk d)) (pubk b))))
    (uniq-orig na0 na1 na2))
  (defrole resp1
    (vars (a b c d name)
      (na0 na1 na2 nb0 nb1 nb2 nc0 nc1 nc2 nd0 nd1 nd2 text))
    (trace
      (recv
        (enc na0 a c d (enc na1 a b d (pubk c)) (enc na2 a b c (pubk d))
          (pubk b)))
      (send
        (enc nb0 b d a (enc na1 a b d (pubk c)) (enc na2 a b c (pubk d))
          (enc nb1 b c a (pubk d)) (enc na0 nb2 b c d (pubk a))
          (pubk c)))
      (recv
        (enc nb2 (enc nb0 nc2 c d a (pubk b))
          (enc nb1 nd1 d a c (pubk b)) (enc nc0 nd2 d a b (pubk c))
          (enc nc1 (pubk c)) (enc nd0 (pubk d)) (pubk b)))
      (send
        (enc nc2 (enc nc0 nd2 d a b (pubk c)) (enc nc1 (pubk c))
          (enc nd0 (pubk d)) (enc nd1 (pubk d)) (pubk c))))
    (uniq-orig nb0 nb1 nb2))
  (defrole resp2
    (vars (a b c d name)
      (na0 na1 na2 nb0 nb1 nb2 nc0 nc1 nc2 nd0 nd1 nd2 text))
    (trace
      (recv
        (enc nb0 b d a (enc na1 a b d (pubk c)) (enc na2 a b c (pubk d))
          (enc nb1 b c a (pubk d)) (enc na0 nb2 b c d (pubk a))
          (pubk c)))
      (send
        (enc nc0 c a b (enc na2 a b c (pubk d)) (enc nb1 b c a (pubk d))
          (enc na0 nb2 b c d (pubk a)) (enc na1 nc1 c b d (pubk a))
          (enc nb0 nc2 c d a (pubk b)) (pubk d)))
      (recv
        (enc nc2 (enc nc0 nd2 d a b (pubk c)) (enc nc1 (pubk c))
          (enc nd0 (pubk d)) (enc nd1 (pubk d)) (pubk c)))
      (send (enc nd2 (enc nd0 (pubk d)) (enc nd1 (pubk d)) (pubk d))))
    (uniq-orig nc0 nc1 nc2))
  (defrole resp3
    (vars (a b c d name)
      (na0 na1 na2 nb0 nb1 nb2 nc0 nc1 nc2 nd0 nd1 nd2 text))
    (trace
      (recv
        (enc nc0 c a b (enc na2 a b c (pubk d)) (enc nb1 b c a (pubk d))
          (enc na0 nb2 b c d (pubk a)) (enc na1 nc1 c b d (pubk a))
          (enc nb0 nc2 c d a (pubk b)) (pubk d)))
      (send
        (enc na2 nd0 d b c (enc na0 nb2 b c d (pubk a))
          (enc na1 nc1 c b d (pubk a)) (enc nb0 nc2 c d a (pubk b))
          (enc nb1 nd1 d a c (pubk b)) (enc nc0 nd2 d a b (pubk c))
          (pubk a)))
      (recv (enc nd2 (enc nd0 (pubk d)) (enc nd1 (pubk d)) (pubk d))))
    (uniq-orig nd0 nd1 nd2)))

(defskeleton nsl4 (vars (a b c d name))
  (defstrand init 3 (a a) (b b) (c c) (d d))
  (non-orig (privk a) (privk b) (privk c) (privk d)))

(defskeleton nsl4 (vars (a b c d name))
  (defstrand resp1 4 (a a) (b b) (c c) (d d))
  (non-orig (privk a) (privk b) (privk c) (privk d)))

(defskeleton nsl4 (vars (a b c d name))
  (defstrand resp2 4 (a a) (b b) (c c) (d d))
  (non-orig (privk a) (privk b) (privk c) (privk d)))

(defskeleton nsl4 (vars (a b c d name))
  (defstrand resp3 3 (a a) (b b) (c c) (d d))
  (non-orig (privk a) (privk b) (privk c) (privk d)))
