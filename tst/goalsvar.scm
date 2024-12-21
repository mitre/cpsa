(herald goalsvar)

;;; Section 1 --- Examples from CPSA and Formal Security Goals

;;; Needham-Schroeder from Section 10 of the CPSA Primer

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace
     (send (enc n1 a (pubk b)))
     (recv (enc n1 n2 (pubk a)))
     (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace
     (recv (enc n1 a (pubk b)))
     (send (enc n1 n2 (pubk a)))
     (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder with no role origination assumptions"))

(defgoal ns
  (forall ((b name) (n1 text) (z0 strd))
    (implies
     (and 
      (strand init z0 3 (n1 n1) (b b))
      (non (privk b)) (uniq n1))
     (exists ((z1 strd))
	     (strand resp z1 2 (b b)))))
  (comment "Initiator point of view")
  (comment "Authentication goal: agreement on name b"))

(defgoal ns
  (forall ((b name) (n1 text) (z0 strd))
    (implies
     (and (strand init z0 3 (n1 n1) (b b))
      (non (privk b)) (uniq n1))
     (exists ((z1 strd))
        (and 
          (strand resp z1 2 (b b))
	      (prec z1 1 z0 2)))))
  (comment "Prec example"))

(defgoal ns
  (forall ((a b name) (n2 text) (z0 strd))
    (implies
     (and (strand resp z0 3 (n2 n2) (a a) (b b))
      (non (privk a)) (uniq n2))
     (exists ((z1 strd))
      (strand init z1 2 (b b)))))
  (comment "Responder point of view")
  (comment "Failed authentication goal: agreement on name b"))

(defprotocol nsl basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace
     (send (enc n1 a (pubk b)))
     (recv (enc n1 n2 b (pubk a)))
     (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace
     (recv (enc n1 a (pubk b)))
     (send (enc n1 n2 b (pubk a)))
     (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder-Lowe with no role origination assumptions"))

(defgoal nsl
  (forall ((a b name) (n2 text) (z0 strd))
    (implies
     (and (strand resp z0 3 (n2 n2) (a a) (b b))
      (non (privk a)) (uniq n2))
     (exists ((z1 strd))
      (strand init z1 2 (b b)))))
  (comment "Responder point of view")
  (comment "Authentication goal: agreement on name b"))

(defgoal ns
  (forall ((a b name) (n1 text) (z0 z1 strd))
    (implies
     (and (strand init z0 3 (n1 n1) (a a) (b b))
      (listener z1 n1)
      (non (privk a)) (non (privk b)) (uniq n1))
     (false)))
  (comment "Initiator point of view")
  (comment "Secrecy goal: nonce n1 not revealed"))

(defprotocol unilateral basic
  (defrole init
    (vars (a name) (n text))
    (trace
     (send (enc n (pubk a)))
     (recv n)))
  (defrole resp
    (vars (a name) (n text))
    (trace
     (recv (enc n (pubk a)))
     (send n)))
  (comment "Unilateral authentication"))

(defgoal unilateral
  (forall ((a name) (n text)
           (z0 strd))
   (implies
    (and (strand init z0 2 (n n) (a a))
     (non (privk a)) (uniq n))
    (exists ((z1 strd))
     (strand resp z1 2 (a a)))))
  (comment "Unilateral authentication goal"))

;;; Does initiator satisfy the unilateral authentication goal?

;;; Note that the goal requires translation of some of the role
;;; specific predicates.
(defgoal ns
  (forall ((a name) (n text) (z0 strd))
   (implies
    (and (strand init z0 2 (n1 n) (b a))
      (non (privk a)) (uniq n))
    (exists ((z1 strd))
     (strand resp z1 2 (b a)))))
  (comment "Initiator authentication goal")
  (comment "Same as unilateral goal under the predicate mapping:")
  (comment (p "init" "n") "->" (p "init" "n1") "and")
  (comment (p "init" "a") "->" (p "init" "b") "and")
  (comment (p "resp" "a") "->" (p "resp" "b")))

;;; Does responder satisfy the unilateral authentication goal?

(defgoal ns
  (forall ((a name) (n text) (z0 strd))
   (implies
    (and (strand resp z0 3 (n2 n) (a a))
     (non (privk a)) (uniq n))
    (exists ((z1 strd))
     (strand init z1 3 (a a)))))
  (comment "Responder authentication goal")
  (comment "Same as unilateral goal under the predicate mapping:")
  (comment (p "init" 1) "->" (p "resp" 2) "and")
  (comment (p "init" "n") "->" (p "resp" "n2") "and")
  (comment (p "init" "a") "->" (p "resp" "a") "and")
  (comment (p "resp" 1) "->" (p "init" 2) "and")
  (comment (p "resp" "a") "->" (p "init" "a")))

(defgoal ns
  (forall ((a b name) (n text) (z0 strd))
    (implies
     (and (strand init z0 2 (n1 n) (a a) (b b))
      (non (privk a)) (non (privk b)) (uniq n))
     (exists ((z1 strd))
      (strand resp z1 2 (b b)))))
  (forall ((a b name) (n text) (z0 strd))
   (implies
     (and (strand init z0 2 (n1 n) (a a) (b b))
      (non (privk a)) (non (privk b)) (uniq n))
     (exists ((z1 strd))
      (strand resp z1 2 (a a)))))
  (comment "Two initiator authentication goals"))

;;; The shape analysis sentence as input (kind of useless)

(defgoal ns
  (forall ((n1 n2 text) (b a name) (z strd))
    (implies
      (and (strand init z 3 (n1 n1) (n2 n2) (a a) (b b))
        (non (privk b))
        (uniq-at n1 z 0))
      (exists ((n2-0 text) (z-0 strd))
        (and (strand resp z-0 2 (n2 n2-0) (n1 n1) (b b) (a a))
          (prec z 0 z-0 0) (prec z-0 1 z 1)))))
  (comment "Shape analysis sentence"))

;;; Section 2 --- Additional Examples

(defgoal ns
  (forall ((a b name) (n2 text) (z0 z1 strd))
    (implies
     (and
      (strand resp z0 3 (n2 n2) (a a) (b b))
      ;; Still have to add support for a listener formula: 
      (listener z1 n2)
      (non (privk a)) (non (privk b)) (uniq n2))
     (false)))
  (comment "Responder point of view")
  (comment "Failed secrecy goal: nonce n2 not revealed"))

;;; Double initiator point of view
(defskeleton ns
  (vars (a b name) (n1 n1-0 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (defstrand init 3 (a a) (b b) (n1 n1-0))
  (non-orig (privk b) (privk a))
  (uniq-orig n1 n1-0)
  (goals
  (forall ((n1 n1-0 n2 n2-0 text) (a b name) (z z-0 strd))
    (implies
      (and 
        (strand init z 3 (n1 n1) (n2 n2) (a a) (b b))
        (strand init z-0 3 (n1 n1-0) (n2 n2-0) (a a) (b b))
        (non (privk a))
        (non (privk b)) (uniq-at n1 z 0) (uniq-at n1-0 z-0 0))
      (= z z-0))))
  (comment "Double initiator point of view"))

(defprotocol nsl-typeless basic
  (defrole init
    (vars (a b name) (n1 text) (n2 mesg))
    (trace
     (send (enc a n1 (pubk b)))
     (recv (enc n1 n2 b (pubk a)))
     (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 text) (n1 mesg))
    (trace
     (recv (enc a n1 (pubk b)))
     (send (enc n1 n2 b (pubk a)))
     (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder-Lowe with untyped nonces"))

;;; The responder point of view
(defgoal nsl-typeless
  (forall ((n2 text) (a b name) (z z-0 strd))
    (implies
      (and (strand resp z 2 (n2 n2) (b b) (a a))
        (listener z-0 n2)
        (non (privk a)) (non (privk b)) (uniq n2))
      (false)))
  (comment "Shows typeflaw in typeless NSL"))
