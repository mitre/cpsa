(herald factvar)

;; An example of a rule that creates a variable that is
;; used in a fact but does not occur in a strand.

(defprotocol free-fact-var basic
  (defrole resp
    (vars (n text) (k akey))
    (trace
     (recv (enc n k))
     (send n)))

  (defrule add
    (forall ((z strd))
	    (implies
	     (p "resp" z 1)
	     (exists ((m text))
		     (fact thing m))))
    (comment "This rule adds a text variable")
    (comment "that does not appear in a strand"))
  )

(defskeleton free-fact-var
  (vars (k akey))
  (defstrand resp 1 (k k))
  (non-orig (invk k)))

(defskeleton free-fact-var
  (vars (n text) (k akey))
  (defstrand resp 1 (n n) (k k))
  (non-orig (invk k))
  (pen-non-orig n))
