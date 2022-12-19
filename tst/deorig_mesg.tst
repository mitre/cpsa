(herald deorig-mesg)

(comment "CPSA 4.4.1")
(comment "All input read from tst/deorig_mesg.scm")

(defprotocol deorig-mesg basic
  (defrole init
    (vars (k akey) (x text))
    (trace (send (enc x k)) (recv x))
    (non-orig (invk k))
    (uniq-orig x))
  (defrole resp (vars (x mesg) (y text)) (trace (recv x) (send y)))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton deorig-mesg
  (vars (x text) (k akey))
  (defstrand init 2 (x x) (k k))
  (non-orig (invk k))
  (uniq-orig x)
  (traces ((send (enc x k)) (recv x)))
  (label 0)
  (unrealized (0 1))
  (dead)
  (origs (x (0 0)))
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol deorig-mesg basic
  (defrole init
    (vars (k akey) (x text))
    (trace (send (enc x k)) (recv x))
    (non-orig (invk k))
    (uniq-orig x))
  (defrole resp (vars (x mesg) (y text)) (trace (recv x) (send y)))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton deorig-mesg
  (vars (z text) (k akey))
  (defstrand init 2 (x z) (k k))
  (defstrand resp 2 (x (enc z k)) (y z))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk k))
  (uniq-orig z)
  (traces ((send (enc z k)) (recv z)) ((recv (enc z k)) (send z)))
  (label 1)
  (realized)
  (shape)
  (maps ((0 1) ((k k) (z z))))
  (origs (z (0 0))))

(comment "Nothing left to do")
