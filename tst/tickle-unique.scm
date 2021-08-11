(herald tickle-unique)

(defprotocol tickle basic
  (defrole init
    (vars (a b name) (na nb text))
    (trace
     (send (enc a na (pubk b)))
     (recv (enc b na na nb (pubk a)))
     (send nb))
    (uniq-orig na))

  (defrole resp
    (vars (a b name) (na nb0 nb text))
    (trace
     (recv (enc a na (pubk b)))
     (send (enc b na nb0 nb (pubk a)))
     (recv nb)))

  (defrule uniq-tickle
    (forall
     ((z strd) (nb0 text))
     (implies
      (and (fact guard-me)
	   (p "resp" z 2)
	   (p "resp" "nb0" z nb0))
      (uniq nb0)))))

(defskeleton tickle
  (vars (a b name) (na nb0 nb text))
  (defstrand resp 3 (a a) (b b) (nb0 nb0) (nb nb))
  (non-orig (privk a))
  (uniq-orig nb))

(defskeleton tickle
  (vars (a b name) (na nb0 nb text))
  (defstrand resp 3 (a a) (b b) (nb0 nb0) (nb nb))
  (facts (guard-me))
  (non-orig (privk a))
  (uniq-orig nb))
