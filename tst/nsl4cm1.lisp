(herald "Four Party Needham-Schroeder-Lowe Protocol")

(defprotocol nsl4cm basic
   (defrole init
      (vars (a b c d name) (na nb nc nd text))
      (trace
         (send (enc a c d na (pubk b)))
	 (recv (enc b c d na nb nc nd (pubk a)))
	 (send (enc nb nc nd (pubk b)))))
   (defrole resp1
      (vars (a b c d name) (na nb nc nd text))
      (trace
         (recv (enc a c d na (pubk b)))
	 (send (enc a b d na nb (pubk c)))
	 (recv (enc nb nc nd (pubk b)))
	 (send (enc nc nd (pubk c)))))
   (defrole resp2
      (vars (a b c d name) (na nb nc nd text))
      (trace
         (recv (enc a b d na nb (pubk c)))
	 (send (enc a b c na nb nc (pubk d)))
	 (recv (enc nc nd (pubk c)))
	 (send (enc nd (pubk d)))))
   (defrole resp3
      (vars (a b c d name) (na nb nc nd text))
      (trace
         (recv (enc a b c na nb nc (pubk d)))
	 (send (enc b c d na nb nc nd (pubk a)))
	 (recv (enc nd (pubk d))))))

(defskeleton nsl4cm (vars (a b c d name) (na text))
  (defstrand init 3 (a a) (b b) (c c) (d d) (na na))
   (non-orig (privk a) (privk b) (privk c) (privk d))
   (uniq-orig na))

(comment (defskeleton nsl4cm (vars (a b c d name) (nb text))
   (defstrand resp1 4 (a a) (b b) (c c) (d d) (nb nb))
   (non-orig (privk a) (privk b) (privk c) (privk d))
   (uniq-orig nb))

(defskeleton nsl4cm (vars (a b c d name) (nc text))
   (defstrand resp2 4 (a a) (b b) (c c) (d d) (nc nc))
   (non-orig (privk a) (privk b) (privk c) (privk d))
   (uniq-orig nc))

(defskeleton nsl4cm (vars (a b c d name) (nd text))
   (defstrand resp3 3 (a a) (b b) (c c) (d d) (nd nd))
   (non-orig (privk a) (privk b) (privk c) (privk d))
   (uniq-orig nd)))
