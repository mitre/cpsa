(herald pfs-via-pubkey)

(comment "CPSA 4.4.3")
(comment "All input read from tst/pfs-via-pubkey.scm")

(defprotocol pfs-easy basic
  (defrole init
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace (send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s (privk "sgn" b)) new-akey))
      (send (privk "sgn" a))))
  (defrole resp
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace (recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton pfs-easy
  (vars (n data) (s text) (new-akey akey) (a b name))
  (defstrand init 3 (n n) (s s) (new-akey new-akey) (a a) (b b))
  (non-orig (invk new-akey) (privk "sgn" b))
  (uniq-orig n new-akey (privk "sgn" a))
  (traces
    ((send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s (privk "sgn" b)) new-akey))
      (send (privk "sgn" a))))
  (label 0)
  (unrealized (0 1))
  (origs ((privk "sgn" a) (0 2)) (new-akey (0 0)) (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pfs-easy
  (vars (n data) (s text) (new-akey new-akey-0 akey) (a b name))
  (defstrand init 3 (n n) (s s) (new-akey new-akey) (a a) (b b))
  (defstrand resp 2 (n n) (s s) (new-akey new-akey-0) (a a) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk new-akey) (privk "sgn" b))
  (uniq-orig n new-akey (privk "sgn" a))
  (operation encryption-test (added-strand resp 2)
    (enc a n s (privk "sgn" b)) (0 1))
  (strand-map 0)
  (traces
    ((send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s (privk "sgn" b)) new-akey))
      (send (privk "sgn" a)))
    ((recv (enc a b new-akey-0 n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey-0))))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pfs-easy
  (vars (n data) (s text) (new-akey akey) (a b name))
  (defstrand init 3 (n n) (s s) (new-akey new-akey) (a a) (b b))
  (defstrand resp 2 (n n) (s s) (new-akey new-akey) (a a) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk new-akey) (privk "sgn" b))
  (uniq-orig n new-akey (privk "sgn" a))
  (operation encryption-test (displaced 2 0 init 1)
    (enc a b new-akey-0 n (privk "sgn" a)) (1 0))
  (strand-map 0 1)
  (traces
    ((send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s (privk "sgn" b)) new-akey))
      (send (privk "sgn" a)))
    ((recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey))))
  (label 2)
  (parent 1)
  (realized)
  (shape)
  (maps ((0) ((new-akey new-akey) (a a) (b b) (n n) (s s))))
  (origs ((privk "sgn" a) (0 2)) (new-akey (0 0)) (n (0 0))))

(comment "Nothing left to do")

(defprotocol pfs-easy basic
  (defrole init
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace (send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s (privk "sgn" b)) new-akey))
      (send (privk "sgn" a))))
  (defrole resp
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace (recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton pfs-easy
  (vars (n data) (s text) (new-akey akey) (a b name))
  (defstrand resp 2 (n n) (s s) (new-akey new-akey) (a a) (b b))
  (non-orig (privk "sgn" a))
  (traces
    ((recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey))))
  (label 3)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pfs-easy
  (vars (n data) (s text) (new-akey akey) (a b name))
  (defstrand resp 2 (n n) (s s) (new-akey new-akey) (a a) (b b))
  (defstrand init 1 (n n) (new-akey new-akey) (a a) (b b))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sgn" a))
  (operation encryption-test (added-strand init 1)
    (enc a b new-akey n (privk "sgn" a)) (0 0))
  (strand-map 0)
  (traces
    ((recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey)))
    ((send (enc a b new-akey n (privk "sgn" a)))))
  (label 4)
  (parent 3)
  (realized)
  (shape)
  (maps ((0) ((new-akey new-akey) (a a) (b b) (n n) (s s))))
  (origs))

(comment "Nothing left to do")

(defprotocol pfs-easy basic
  (defrole init
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace (send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s (privk "sgn" b)) new-akey))
      (send (privk "sgn" a))))
  (defrole resp
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace (recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton pfs-easy
  (vars (n data) (s s-0 text) (new-akey akey) (a b name))
  (defstrand resp 2 (n n) (s s) (new-akey new-akey) (a a) (b b))
  (defstrand init 3 (n n) (s s-0) (new-akey new-akey) (a a) (b b))
  (deflistener s)
  (precedes ((1 0) (0 0)))
  (non-orig (invk new-akey))
  (uniq-orig s (privk "sgn" a))
  (traces
    ((recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey)))
    ((send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s-0 (privk "sgn" b)) new-akey))
      (send (privk "sgn" a))) ((recv s) (send s)))
  (label 5)
  (unrealized (2 0))
  (preskeleton)
  (origs ((privk "sgn" a) (1 2)) (s (0 1)))
  (comment "Not a skeleton"))

(defskeleton pfs-easy
  (vars (n data) (s s-0 text) (new-akey akey) (a b name))
  (defstrand resp 2 (n n) (s s) (new-akey new-akey) (a a) (b b))
  (defstrand init 3 (n n) (s s-0) (new-akey new-akey) (a a) (b b))
  (deflistener s)
  (precedes ((0 1) (2 0)) ((1 0) (0 0)))
  (non-orig (invk new-akey))
  (uniq-orig s (privk "sgn" a))
  (traces
    ((recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey)))
    ((send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s-0 (privk "sgn" b)) new-akey))
      (send (privk "sgn" a))) ((recv s) (send s)))
  (label 6)
  (parent 5)
  (unrealized (2 0))
  (dead)
  (origs ((privk "sgn" a) (1 2)) (s (0 1)))
  (comment "empty cohort"))

(comment "Nothing left to do")
