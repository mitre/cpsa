(defprotocol tnsl5 basic
  (defrole init
    (vars (a b c d e name)
      (na0 na1 na2 na3 nb0 nb1 nb2 nb3 nc0 nc1 nc2 nc3 nd0 nd1 nd2 nd3
        ne0 ne1 ne2 ne3 text))
    (trace
      (send
        (enc na0 a c d e (enc "unitac" na1 a b d e (pubk c))
          (enc "unitad" na2 a b c e (pubk d))
          (enc "unitae" na3 a b c d (pubk e)) (pubk b)))
      (recv
        (enc na3 ne0 e b c d (enc "repba" na0 nb3 b c d e (pubk a))
          (enc "repca" na1 nc2 c b d e (pubk a))
          (enc "repda" na2 nd1 d e b c (pubk a))
          (enc "repcb" nb0 nc3 c d e a (pubk b))
          (enc "repdb" nb1 nd2 d c e a (pubk b))
          (enc "repeb" nb2 ne1 e a c d (pubk b))
          (enc "repdc" nc0 nd3 d e a b (pubk c))
          (enc "repec" nc1 ne2 e a b d (pubk c))
          (enc "reped" nd0 ne3 e a b c (pubk d)) (pubk a)))
      (send
        (enc nb3 (enc "repcb" nb0 nc3 c d e a (pubk b))
          (enc "repdb" nb1 nd2 d c e a (pubk b))
          (enc "repeb" nb2 ne1 e a c d (pubk b))
          (enc "repdc" nc0 nd3 d e a b (pubk c))
          (enc "repec" nc1 ne2 e a b d (pubk c))
          (enc "confac" nc2 (pubk c))
          (enc "reped" nd0 ne3 e a b c (pubk d))
          (enc "confad" nd1 (pubk d)) (enc "confae" ne0 (pubk e))
          (pubk b))))
    (uniq-orig na0 na1 na2 na3))
  (defrole resp1
    (vars (a b c d e name)
      (na0 na1 na2 na3 nb0 nb1 nb2 nb3 nc0 nc1 nc2 nc3 nd0 nd1 nd2 nd3
        ne0 ne1 ne2 ne3 text))
    (trace
      (recv
        (enc na0 a c d e (enc "unitac" na1 a b d e (pubk c))
          (enc "unitad" na2 a b c e (pubk d))
          (enc "unitae" na3 a b c d (pubk e)) (pubk b)))
      (send
        (enc nb0 b d e a (enc "unitac" na1 a b d e (pubk c))
          (enc "unitad" na2 a b c e (pubk d))
          (enc "unitbd" nb1 b c e a (pubk d))
          (enc "unitae" na3 a b c d (pubk e))
          (enc "unitbe" nb2 b c d a (pubk e))
          (enc "repba" na0 nb3 b c d e (pubk a)) (pubk c)))
      (recv
        (enc nb3 (enc "repcb" nb0 nc3 c d e a (pubk b))
          (enc "repdb" nb1 nd2 d c e a (pubk b))
          (enc "repeb" nb2 ne1 e a c d (pubk b))
          (enc "repdc" nc0 nd3 d e a b (pubk c))
          (enc "repec" nc1 ne2 e a b d (pubk c))
          (enc "confac" nc2 (pubk c))
          (enc "reped" nd0 ne3 e a b c (pubk d))
          (enc "confad" nd1 (pubk d)) (enc "confae" ne0 (pubk e))
          (pubk b)))
      (send
        (enc nc3 (enc "repdc" nc0 nd3 d e a b (pubk c))
          (enc "repec" nc1 ne2 e a b d (pubk c))
          (enc "confac" nc2 (pubk c))
          (enc "reped" nd0 ne3 e a b c (pubk d))
          (enc "confad" nd1 (pubk d)) (enc "confbd" nd2 (pubk d))
          (enc "confae" ne0 (pubk e)) (enc "confbe" ne1 (pubk e))
          (pubk c))))
    (uniq-orig nb0 nb1 nb2 nb3))
  (defrole resp2
    (vars (a b c d e name)
      (na0 na1 na2 na3 nb0 nb1 nb2 nb3 nc0 nc1 nc2 nc3 nd0 nd1 nd2 nd3
        ne0 ne1 ne2 ne3 text))
    (trace
      (recv
        (enc nb0 b d e a (enc "unitac" na1 a b d e (pubk c))
          (enc "unitad" na2 a b c e (pubk d))
          (enc "unitbd" nb1 b c e a (pubk d))
          (enc "unitae" na3 a b c d (pubk e))
          (enc "unitbe" nb2 b c d a (pubk e))
          (enc "repba" na0 nb3 b c d e (pubk a)) (pubk c)))
      (send
        (enc nc0 c e a b (enc "unitad" na2 a b c e (pubk d))
          (enc "unitbd" nb1 b c e a (pubk d))
          (enc "unitae" na3 a b c d (pubk e))
          (enc "unitbe" nb2 b c d a (pubk e))
          (enc "unitce" nc1 c d a b (pubk e))
          (enc "repba" na0 nb3 b c d e (pubk a))
          (enc "repca" na1 nc2 c b d e (pubk a))
          (enc "repcb" nb0 nc3 c d e a (pubk b)) (pubk d)))
      (recv
        (enc nc3 (enc "repdc" nc0 nd3 d e a b (pubk c))
          (enc "repec" nc1 ne2 e a b d (pubk c))
          (enc "confac" nc2 (pubk c))
          (enc "reped" nd0 ne3 e a b c (pubk d))
          (enc "confad" nd1 (pubk d)) (enc "confbd" nd2 (pubk d))
          (enc "confae" ne0 (pubk e)) (enc "confbe" ne1 (pubk e))
          (pubk c)))
      (send
        (enc nd3 (enc "reped" nd0 ne3 e a b c (pubk d))
          (enc "confad" nd1 (pubk d)) (enc "confbd" nd2 (pubk d))
          (enc "confae" ne0 (pubk e)) (enc "confbe" ne1 (pubk e))
          (enc "confce" ne2 (pubk e)) (pubk d))))
    (uniq-orig nc0 nc1 nc2 nc3))
  (defrole resp3
    (vars (a b c d e name)
      (na0 na1 na2 na3 nb0 nb1 nb2 nb3 nc0 nc1 nc2 nc3 nd0 nd1 nd2 nd3
        ne0 ne1 ne2 ne3 text))
    (trace
      (recv
        (enc nc0 c e a b (enc "unitad" na2 a b c e (pubk d))
          (enc "unitbd" nb1 b c e a (pubk d))
          (enc "unitae" na3 a b c d (pubk e))
          (enc "unitbe" nb2 b c d a (pubk e))
          (enc "unitce" nc1 c d a b (pubk e))
          (enc "repba" na0 nb3 b c d e (pubk a))
          (enc "repca" na1 nc2 c b d e (pubk a))
          (enc "repcb" nb0 nc3 c d e a (pubk b)) (pubk d)))
      (send
        (enc nd0 d a b c (enc "unitae" na3 a b c d (pubk e))
          (enc "unitbe" nb2 b c d a (pubk e))
          (enc "unitce" nc1 c d a b (pubk e))
          (enc "repba" na0 nb3 b c d e (pubk a))
          (enc "repca" na1 nc2 c b d e (pubk a))
          (enc "repda" na2 nd1 d e b c (pubk a))
          (enc "repcb" nb0 nc3 c d e a (pubk b))
          (enc "repdb" nb1 nd2 d c e a (pubk b))
          (enc "repde" nc0 nd3 d e a b (pubk c)) (pubk e)))
      (recv
        (enc nd3 (enc "reped" nd0 ne3 e a b c (pubk d))
          (enc "confad" nd1 (pubk d)) (enc "confbd" nd2 (pubk d))
          (enc "confae" ne0 (pubk e)) (enc "confbe" ne1 (pubk e))
          (enc "confce" ne2 (pubk e)) (pubk d)))
      (send
        (enc ne3 (enc "confae" ne0 (pubk e)) (enc "confbe" ne1 (pubk e))
          (enc "confce" ne2 (pubk e)) (pubk e))))
    (uniq-orig nd0 nd1 nd2 nd3))
  (defrole resp4
    (vars (a b c d e name)
      (na0 na1 na2 na3 nb0 nb1 nb2 nb3 nc0 nc1 nc2 nc3 nd0 nd1 nd2 nd3
        ne0 ne1 ne2 ne3 text))
    (trace
      (recv
        (enc nd0 d a b c (enc "unitae" na3 a b c d (pubk e))
          (enc "unitbe" nb2 b c d a (pubk e))
          (enc "unitce" nc1 c d a b (pubk e))
          (enc "repba" na0 nb3 b c d e (pubk a))
          (enc "repca" na1 nc2 c b d e (pubk a))
          (enc "repda" na2 nd1 d e b c (pubk a))
          (enc "repcb" nb0 nc3 c d e a (pubk b))
          (enc "repdb" nb1 nd2 d c e a (pubk b))
          (enc "repde" nc0 nd3 d e a b (pubk c)) (pubk e)))
      (send
        (enc na3 ne0 e b c d (enc "repba" na0 nb3 b c d e (pubk a))
          (enc "repca" na1 nc2 c b d e (pubk a))
          (enc "repda" na2 nd1 d e b c (pubk a))
          (enc "repcb" nb0 nc3 c d e a (pubk b))
          (enc "repdb" nb1 nd2 d c e a (pubk b))
          (enc "repeb" nb2 ne1 e a c d (pubk b))
          (enc "repdc" nc0 nd3 d e a b (pubk c))
          (enc "repec" nc1 ne2 e a b d (pubk c))
          (enc "reped" nd0 ne3 e a b c (pubk d)) (pubk a)))
      (recv
        (enc ne3 (enc "confae" ne0 (pubk e)) (enc "confbe" ne1 (pubk e))
          (enc "confce" ne2 (pubk e)) (pubk e))))
    (uniq-orig ne0 ne1 ne2 ne3)))

(defskeleton tnsl5
  (vars (a b c d e name))
  (defstrand init 3 (a a) (b b) (c c) (d d) (e e))
  (non-orig (privk a) (privk b) (privk c) (privk d) (privk e)))
