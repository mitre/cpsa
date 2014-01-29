(defprotocol nsl5i basic
  (defrole init
    (vars (a name) (b name) (c name) (d name) (e name) (na text) (nb text) (nc text) (nd text) (ne text))
    (trace
      (send (enc (cat a b c d e (enc (enc (enc na (pubk e)) (pubk d)) (pubk c))) (pubk b)))
      (recv (enc (cat a b c d e na (enc nb (pubk a)) (enc (enc nc (pubk b)) (pubk a)) (enc (enc (enc nd (pubk c)) (pubk b)) (pubk a)) (enc (enc (enc ne (pubk d)) (pubk c)) (pubk b))) (pubk a)))
      (send (enc (cat nb (enc nc (pubk b)) (enc (enc nd (pubk c)) (pubk b)) (enc (enc (enc ne (pubk d)) (pubk c)) (pubk b))) (pubk b))))
      (uniq-orig na))
  (defrole resp1
    (vars (a name) (b name) (c name) (d name) (e name) (na text) (nb text) (nc text) (nd text) (ne text))
    (trace
      (recv (enc (cat a b c d e (enc (enc (enc na (pubk e)) (pubk d)) (pubk c))) (pubk b)))
      (send (enc (cat a b c d e (enc (enc (enc na (pubk e)) (pubk d)) (pubk c)) (enc (enc (enc nb (pubk a)) (pubk e)) (pubk d))) (pubk c)))
      (recv (enc (cat nb (enc nc (pubk b)) (enc (enc nd (pubk c)) (pubk b)) (enc (enc (enc ne (pubk d)) (pubk c)) (pubk b))) (pubk b)))
      (send (enc (cat nc (enc nd (pubk c)) (enc (enc ne (pubk d)) (pubk c))) (pubk c))))
      (uniq-orig nb))
  (defrole resp2
    (vars (a name) (b name) (c name) (d name) (e name) (na text) (nb text) (nc text) (nd text) (ne text))
    (trace
      (recv (enc (cat a b c d e (enc (enc (enc na (pubk e)) (pubk d)) (pubk c)) (enc (enc (enc nb (pubk a)) (pubk e)) (pubk d))) (pubk c)))
      (send (enc (cat a b c d e (enc (enc na (pubk e)) (pubk d)) (enc (enc (enc nb (pubk a)) (pubk e)) (pubk d)) (enc (enc (enc nc (pubk b)) (pubk a)) (pubk e))) (pubk d)))
      (recv (enc (cat nc (enc nd (pubk c)) (enc (enc ne (pubk d)) (pubk c))) (pubk c)))
      (send (enc (cat nd (enc ne (pubk d))) (pubk d))))
      (uniq-orig nc))
  (defrole resp3
    (vars (a name) (b name) (c name) (d name) (e name) (na text) (nb text) (nc text) (nd text) (ne text))
    (trace
      (recv (enc (cat a b c d e (enc (enc na (pubk e)) (pubk d)) (enc (enc (enc nb (pubk a)) (pubk e)) (pubk d)) (enc (enc (enc nc (pubk b)) (pubk a)) (pubk e))) (pubk d)))
      (send (enc (cat a b c d e (enc na (pubk e)) (enc (enc nb (pubk a)) (pubk e)) (enc (enc (enc nc (pubk b)) (pubk a)) (pubk e)) (enc (enc (enc nd (pubk c)) (pubk b)) (pubk a))) (pubk e)))
      (recv (enc (cat nd (enc ne (pubk d))) (pubk d)))
      (send (enc ne (pubk e))))
      (uniq-orig nd))
  (defrole resp4
    (vars (a name) (b name) (c name) (d name) (e name) (na text) (nb text) (nc text) (nd text) (ne text))
    (trace
      (recv (enc (cat a b c d e (enc na (pubk e)) (enc (enc nb (pubk a)) (pubk e)) (enc (enc (enc nc (pubk b)) (pubk a)) (pubk e)) (enc (enc (enc nd (pubk c)) (pubk b)) (pubk a))) (pubk e)))
      (send (enc (cat a b c d e na (enc nb (pubk a)) (enc (enc nc (pubk b)) (pubk a)) (enc (enc (enc nd (pubk c)) (pubk b)) (pubk a)) (enc (enc (enc ne (pubk d)) (pubk c)) (pubk b))) (pubk a)))
      (recv (enc ne (pubk e))))
      (uniq-orig ne)))

(defskeleton nsl5i
  (vars (a name) (b name) (c name) (d name) (e name) (na text) (nb text) (nc text) (nd text) (ne text))
  (defstrand init 3 (a a) (b b) (c c) (d d) (e e))
  (non-orig (privk a) (privk b) (privk c) (privk d) (privk e)))

(defskeleton nsl5i
  (vars (a name) (b name) (c name) (d name) (e name) (na text) (nb text) (nc text) (nd text) (ne text))
  (defstrand resp1 4 (a a) (b b) (c c) (d d) (e e))
  (non-orig (privk a) (privk b) (privk c) (privk d) (privk e)))

(defskeleton nsl5i
  (vars (a name) (b name) (c name) (d name) (e name) (na text) (nb text) (nc text) (nd text) (ne text))
  (defstrand resp2 4 (a a) (b b) (c c) (d d) (e e))
  (non-orig (privk a) (privk b) (privk c) (privk d) (privk e)))

(defskeleton nsl5i
  (vars (a name) (b name) (c name) (d name) (e name) (na text) (nb text) (nc text) (nd text) (ne text))
  (defstrand resp3 4 (a a) (b b) (c c) (d d) (e e))
  (non-orig (privk a) (privk b) (privk c) (privk d) (privk e)))

(defskeleton nsl5i
  (vars (a name) (b name) (c name) (d name) (e name) (na text) (nb text) (nc text) (nd text) (ne text))
  (defstrand resp4 3 (a a) (b b) (c c) (d d) (e e))
  (non-orig (privk a) (privk b) (privk c) (privk d) (privk e)))
