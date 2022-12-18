(herald "Blanchet's Simple Example Protocol"
  (comment "There is a flaw in this protocol by design"))

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

(comment "All input read from blanchet.scm")

(defprotocol blanchet basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Blanchet's protocol"))

(defgoal blanchet
  (forall ((d data) (s skey) (a b akey) (z strd))
    (implies
      (and (p "init" z 2) (p "init" "d" z d) (p "init" "s" z s)
        (p "init" "a" z a) (p "init" "b" z b) (non (invk b))
        (uniq-at s z 0))
      (exists ((z-0 strd))
        (and (p "resp" z-0 2) (p "resp" "d" z-0 d) (p "resp" "s" z-0 s)
          (p "resp" "a" z-0 a) (p "resp" "b" z-0 b) (prec z 0 z-0 0)
          (prec z-0 1 z 1) (uniq-at d z-0 1))))))

(defprotocol blanchet basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Blanchet's protocol"))

(defgoal blanchet
  (forall ((d data) (s skey) (a b akey) (z strd))
    (implies
      (and (p "resp" z 2) (p "resp" "d" z d) (p "resp" "s" z s)
        (p "resp" "a" z a) (p "resp" "b" z b) (non (invk a))
        (non (invk b)) (uniq-at d z 1))
      (exists ((b-0 akey) (z-0 strd))
        (and (p "init" z-0 1) (p "init" "s" z-0 s) (p "init" "a" z-0 a)
          (p "init" "b" z-0 b-0) (prec z-0 0 z 0) (uniq-at s z-0 0))))))

(defprotocol blanchet basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Blanchet's protocol"))

(defgoal blanchet
  (forall ((d data) (s skey) (a b akey) (z z-0 strd))
    (implies
      (and (p "init" z 2) (p "" z-0 2) (p "init" "d" z d)
        (p "init" "s" z s) (p "init" "a" z a) (p "init" "b" z b)
        (p "" "x" z-0 d) (non (invk b)) (uniq-at s z 0))
      (false))))

(defprotocol blanchet basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Blanchet's protocol"))

(defgoal blanchet
  (forall ((d data) (s skey) (a b akey) (z z-0 strd))
    (implies
      (and (p "resp" z 2) (p "" z-0 2) (p "resp" "d" z d)
        (p "resp" "s" z s) (p "resp" "a" z a) (p "resp" "b" z b)
        (p "" "x" z-0 d) (non (invk a)) (non (invk b)) (uniq-at d z 1))
      (exists ((b-0 akey) (z-1 strd))
        (and (p "init" z-1 1) (p "init" "s" z-1 s) (p "init" "a" z-1 a)
          (p "init" "b" z-1 b-0) (prec z 1 z-0 0) (prec z-1 0 z 0)
          (uniq-at s z-1 0))))))

(defprotocol blanchet-corrected basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Corrected Blanchet's protocol"))

(defgoal blanchet-corrected
  (forall ((d data) (s skey) (a b akey) (z strd))
    (implies
      (and (p "init" z 2) (p "init" "d" z d) (p "init" "s" z s)
        (p "init" "a" z a) (p "init" "b" z b) (non (invk b))
        (uniq-at s z 0))
      (exists ((z-0 strd))
        (and (p "resp" z-0 2) (p "resp" "d" z-0 d) (p "resp" "s" z-0 s)
          (p "resp" "a" z-0 a) (p "resp" "b" z-0 b) (prec z 0 z-0 0)
          (prec z-0 1 z 1) (uniq-at d z-0 1))))))

(defprotocol blanchet-corrected basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Corrected Blanchet's protocol"))

(defgoal blanchet-corrected
  (forall ((d data) (s skey) (a b akey) (z z-0 strd))
    (implies
      (and (p "init" z 2) (p "" z-0 2) (p "init" "d" z d)
        (p "init" "s" z s) (p "init" "a" z a) (p "init" "b" z b)
        (p "" "x" z-0 d) (non (invk b)) (uniq-at s z 0))
      (false))))

(defprotocol blanchet-corrected basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Corrected Blanchet's protocol"))

(defgoal blanchet-corrected
  (forall ((d data) (s skey) (a b akey) (z strd))
    (implies
      (and (p "resp" z 2) (p "resp" "d" z d) (p "resp" "s" z s)
        (p "resp" "a" z a) (p "resp" "b" z b) (non (invk a))
        (non (invk b)) (uniq-at d z 1))
      (exists ((z-0 strd))
        (and (p "init" z-0 1) (p "init" "s" z-0 s) (p "init" "a" z-0 a)
          (p "init" "b" z-0 b) (prec z-0 0 z 0) (uniq-at s z-0 0))))))

(defprotocol blanchet-corrected basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Corrected Blanchet's protocol"))

(defgoal blanchet-corrected
  (forall ((d data) (s skey) (a b akey) (z z-0 strd))
    (implies
      (and (p "resp" z 2) (p "" z-0 2) (p "resp" "d" z d)
        (p "resp" "s" z s) (p "resp" "a" z a) (p "resp" "b" z b)
        (p "" "x" z-0 d) (non (invk a)) (non (invk b)) (uniq-at d z 1))
      (false))))
