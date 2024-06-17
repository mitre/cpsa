(herald factvar)

(comment "CPSA 4.4.4")
(comment "All input read from tst/factvar.scm")

(defprotocol free-fact-var basic
  (defrole resp
    (vars (n text) (k akey))
    (trace (recv (enc n k)) (send n)))
  (defrule add
    (forall ((z strd))
      (implies (p "resp" z (idx 1)) (exists ((m text)) (fact thing m))))
    (comment "This rule adds a text variable")
    (comment "that does not appear in a strand"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton free-fact-var
  (vars (n text) (k akey))
  (defstrand resp 1 (n n) (k k))
  (non-orig (invk k))
  (traces ((recv (enc n k))))
  (label 0)
  (realized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton free-fact-var
  (vars (m n text) (k akey))
  (defstrand resp 1 (n n) (k k))
  (non-orig (invk k))
  (facts (thing m))
  (rule add)
  (traces ((recv (enc n k))))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((k k) (n n))))
  (origs))

(comment "Nothing left to do")

(defprotocol free-fact-var basic
  (defrole resp
    (vars (n text) (k akey))
    (trace (recv (enc n k)) (send n)))
  (defrule add
    (forall ((z strd))
      (implies (p "resp" z (idx 1)) (exists ((m text)) (fact thing m))))
    (comment "This rule adds a text variable")
    (comment "that does not appear in a strand"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton free-fact-var
  (vars (n text) (k akey))
  (defstrand resp 1 (n n) (k k))
  (non-orig (invk k))
  (pen-non-orig n)
  (traces ((recv (enc n k))))
  (label 2)
  (unrealized (0 0))
  (origs)
  (comment "Not closed under rules"))

(defskeleton free-fact-var
  (vars (m n text) (k akey))
  (defstrand resp 1 (n n) (k k))
  (non-orig (invk k))
  (pen-non-orig n)
  (facts (thing m))
  (rule add)
  (traces ((recv (enc n k))))
  (label 3)
  (parent 2)
  (unrealized (0 0))
  (dead)
  (origs)
  (comment "empty cohort"))

(comment "Nothing left to do")
