(herald trust-anchor
  (comment "Tests rule application on initial skeleton"))

(comment "CPSA 4.1.1")
(comment "All input read from trust-anchor.scm")

(defprotocol trust-anchor basic
  (defule trust-anchor-inverse-is-non
    (forall ((k akey)) (implies (fact trust-anchor k) (non (invk k))))))

(defskeleton trust-anchor
  (vars (f ca name))
  (deflistener (enc f (pubk f) (privk ca)))
  (non-orig (privk ca))
  (traces
    ((recv (enc f (pubk f) (privk ca)))
      (send (enc f (pubk f) (privk ca)))))
  (label 0)
  (unrealized (0 0))
  (origs)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol trust-anchor basic
  (defule trust-anchor-inverse-is-non
    (forall ((k akey)) (implies (fact trust-anchor k) (non (invk k))))))

(defskeleton trust-anchor
  (vars (f ca name))
  (deflistener (enc f (pubk f) (privk ca)))
  (facts (trust-anchor (pubk ca)))
  (traces
    ((recv (enc f (pubk f) (privk ca)))
      (send (enc f (pubk f) (privk ca)))))
  (label 1)
  (unrealized)
  (shape)
  (maps ((0) ((f f) (ca ca))))
  (origs))

(comment "Nothing left to do")
