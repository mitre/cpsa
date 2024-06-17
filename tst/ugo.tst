(herald uniq-gen-and-orig-example
  (comment "Non-executable role examples"))

(comment "CPSA 4.4.4")
(comment "All input read from tst/ugo.scm")

(defprotocol uniq-gen-example basic
  (defrole init
    (vars (u akey) (k skey))
    (trace (send (enc u k)) (recv (invk u)) (send u))
    (non-orig k)
    (uniq-gen u)
    (comment "Instances of this role generate u and (invk u)"
      "at their first event."))
  (defrole resp
    (vars (u akey) (k skey))
    (trace (recv (enc u k)) (send (invk u)) (recv u))
    (non-orig k)
    (comment "Instances of this role appear to generate (invk u)"
      "at their second event."))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton uniq-gen-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (non-orig k)
  (comment "How is the responder able to send (invk u)?")
  (traces ((recv (enc u k)) (send (invk u)) (recv u)))
  (label 0)
  (unrealized (0 0))
  (dead)
  (origs)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol uniq-gen-example basic
  (defrole init
    (vars (u akey) (k skey))
    (trace (send (enc u k)) (recv (invk u)) (send u))
    (non-orig k)
    (uniq-gen u)
    (comment "Instances of this role generate u and (invk u)"
      "at their first event."))
  (defrole resp
    (vars (u akey) (k skey))
    (trace (recv (enc u k)) (send (invk u)) (recv u))
    (non-orig k)
    (comment "Instances of this role appear to generate (invk u)"
      "at their second event."))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton uniq-gen-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (non-orig k)
  (uniq-gen (invk u))
  (comment "How is the responder able to send (invk u)?")
  (traces ((recv (enc u k)) (send (invk u)) (recv u)))
  (label 1)
  (unrealized (0 0))
  (dead)
  (origs)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol uniq-gen-example-alt basic
  (defrole init
    (vars (u akey) (k skey))
    (trace (send (enc (invk u) k)) (recv u) (send u))
    (non-orig k)
    (uniq-gen (invk u))
    (comment "Instances of this role generate u and (invk u)"
      "at their first event."))
  (defrole resp
    (vars (u akey) (k skey))
    (trace (recv (enc (invk u) k)) (send u) (recv u))
    (non-orig k)
    (comment "Instances of this role appear to generate (invk u)"
      "at their second event."))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton uniq-gen-example-alt
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (non-orig k)
  (comment "How is the responder able to send (invk u)?")
  (traces ((recv (enc (invk u) k)) (send u) (recv u)))
  (label 2)
  (unrealized (0 0))
  (dead)
  (origs)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol uniq-gen-example-alt basic
  (defrole init
    (vars (u akey) (k skey))
    (trace (send (enc (invk u) k)) (recv u) (send u))
    (non-orig k)
    (uniq-gen (invk u))
    (comment "Instances of this role generate u and (invk u)"
      "at their first event."))
  (defrole resp
    (vars (u akey) (k skey))
    (trace (recv (enc (invk u) k)) (send u) (recv u))
    (non-orig k)
    (comment "Instances of this role appear to generate (invk u)"
      "at their second event."))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton uniq-gen-example-alt
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (non-orig k)
  (uniq-gen (invk u))
  (comment "How is the responder able to send (invk u)?")
  (traces ((recv (enc (invk u) k)) (send u) (recv u)))
  (label 3)
  (unrealized (0 0))
  (dead)
  (origs)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol uniq-orig-example basic
  (defrole init
    (vars (u akey) (k skey))
    (trace (send (enc u k)) (recv (invk u)) (send u))
    (non-orig k)
    (uniq-orig u))
  (defrole resp
    (vars (u akey) (k skey))
    (trace (recv (enc u k)) (send (invk u)) (recv u))
    (non-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment
    "Similar to the above, but with uniq-orig instead of uniq-gen."))

(defskeleton uniq-orig-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (non-orig k)
  (traces ((recv (enc u k)) (send (invk u)) (recv u)))
  (label 4)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton uniq-orig-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 1 (k k) (u u))
  (precedes ((1 0) (0 0)))
  (non-orig k)
  (uniq-orig u)
  (operation encryption-test (added-strand init 1) (enc u k) (0 0))
  (strand-map 0)
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k))))
  (label 5)
  (parent 4)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton uniq-orig-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 3 (k k) (u u))
  (precedes ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig k)
  (uniq-orig u)
  (operation nonce-test (displaced 1 2 init 3) u (0 2) (enc u k))
  (strand-map 0 1)
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k)) (recv (invk u)) (send u)))
  (label 6)
  (parent 5)
  (realized)
  (shape)
  (maps ((0) ((u u) (k k))))
  (origs (u (1 0))))

(comment "Nothing left to do")

(defprotocol uniq-orig-example basic
  (defrole init
    (vars (u akey) (k skey))
    (trace (send (enc u k)) (recv (invk u)) (send u))
    (non-orig k)
    (uniq-orig u))
  (defrole resp
    (vars (u akey) (k skey))
    (trace (recv (enc u k)) (send (invk u)) (recv u))
    (non-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment
    "Similar to the above, but with uniq-orig instead of uniq-gen."))

(defskeleton uniq-orig-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (non-orig k)
  (uniq-orig (invk u))
  (traces ((recv (enc u k)) (send (invk u)) (recv u)))
  (label 7)
  (unrealized (0 0))
  (origs ((invk u) (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton uniq-orig-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 1 (k k) (u u))
  (precedes ((1 0) (0 0)))
  (non-orig k)
  (uniq-orig u (invk u))
  (operation encryption-test (added-strand init 1) (enc u k) (0 0))
  (strand-map 0)
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k))))
  (label 8)
  (parent 7)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton uniq-orig-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 3 (k k) (u u))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig k)
  (uniq-orig u (invk u))
  (operation nonce-test (displaced 1 2 init 3) u (0 2) (enc u k))
  (strand-map 0 1)
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k)) (recv (invk u)) (send u)))
  (label 9)
  (parent 8)
  (realized)
  (shape)
  (maps ((0) ((u u) (k k))))
  (origs (u (1 0)) ((invk u) (0 1))))

(comment "Nothing left to do")
