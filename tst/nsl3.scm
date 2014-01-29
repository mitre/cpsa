(herald "Three Party Needham-Schroeder-Lowe Protocol")

(defprotocol nsl3 basic
  (defrole init (vars (a b c name) (na0 na1 nb0 nb1 nc0 nc1 text))
    (trace
     (send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
     (recv (enc na1 nc1 c b
		(enc na0 nb0 b c (pubk a))
		(enc nb1 nc0 c a (pubk b))
		(pubk a)))
     (send (enc nb0
		(enc nb1 nc0 c a (pubk b))
		(enc nc1 (pubk c))
		(pubk b))))
    (uniq-orig na0 na1))
  (defrole mid (vars (a b c name) (na0 na1 nb0 nb1 nc0 nc1 text))
    (trace
     (recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
     (send (enc nb1 b a
		(enc na1 a b (pubk c))
		(enc na0 nb0 b c (pubk a))
		(pubk c)))
     (recv (enc nb0
		(enc nb1 nc0 c a (pubk b))
		(enc nc1 (pubk c))
		(pubk b)))
     (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    (uniq-orig nb0 nb1))
  (defrole resp (vars (a b c name) (na0 na1 nb0 nb1 nc0 nc1 text))
    (trace
     (recv (enc nb1 b a
		(enc na1 a b (pubk c))
		(enc na0 nb0 b c (pubk a))
		(pubk c)))
     (send (enc na1 nc1 c b
		(enc na0 nb0 b c (pubk a))
		(enc nb1 nc0 c a (pubk b))
		(pubk a)))
     (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    (uniq-orig nc0 nc1)))

(defskeleton nsl3
  (vars (a b c name))
  (defstrand init 3 (a a) (b b) (c c))
  (non-orig (privk a) (privk b) (privk c)))

(defskeleton nsl3
  (vars (a b c name))
  (defstrand mid 4 (a a) (b b) (c c))
  (non-orig (privk a) (privk b) (privk c)))

(defskeleton nsl3
  (vars (a b c name))
  (defstrand resp 3 (a a) (b b) (c c))
  (non-orig (privk a) (privk b) (privk c)))
