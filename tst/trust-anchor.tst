(herald trust-anchor
  (comment "Tests rule application on initial skeleton"))

(comment "CPSA 4.4.3")
(comment "All input read from tst/trust-anchor.scm")

(defprotocol trust-anchor basic
  (defrule trust-anchor-inverse-is-non
    (forall ((k akey)) (implies (fact trust-anchor k) (non (invk k)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton trust-anchor
  (vars (f ca name))
  (deflistener (enc f (pubk f) (privk ca)))
  (non-orig (privk ca))
  (traces
    ((recv (enc f (pubk f) (privk ca)))
      (send (enc f (pubk f) (privk ca)))))
  (label 0)
  (unrealized (0 0))
  (dead)
  (origs)
  (ugens)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol trust-anchor basic
  (defrule trust-anchor-inverse-is-non
    (forall ((k akey)) (implies (fact trust-anchor k) (non (invk k)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton trust-anchor
  (vars (f ca name))
  (deflistener (enc f (pubk f) (privk ca)))
  (facts (trust-anchor (pubk ca)))
  (traces
    ((recv (enc f (pubk f) (privk ca)))
      (send (enc f (pubk f) (privk ca)))))
  (label 1)
  (realized)
  (origs)
  (ugens)
  (comment "Not closed under rules"))

(defskeleton trust-anchor
  (vars (f ca name))
  (deflistener (enc f (pubk f) (privk ca)))
  (non-orig (privk ca))
  (facts (trust-anchor (pubk ca)))
  (rule trust-anchor-inverse-is-non)
  (traces
    ((recv (enc f (pubk f) (privk ca)))
      (send (enc f (pubk f) (privk ca)))))
  (label 2)
  (parent 1)
  (unrealized (0 0))
  (dead)
  (origs)
  (ugens)
  (comment "empty cohort"))

(comment "Nothing left to do")
