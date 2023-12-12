(herald uniq-gen-and-orig-example
  (comment "Non-executable role examples"))

(comment "CPSA 4.4.3")
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
  (origs)
  (ugens)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton uniq-gen-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 1 (k k) (u u))
  (precedes ((1 0) (0 0)))
  (non-orig k)
  (uniq-gen u)
  (operation encryption-test (added-strand init 1) (enc u k) (0 0))
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k))))
  (label 1)
  (parent 0)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton uniq-gen-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 3 (k k) (u u))
  (precedes ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig k)
  (uniq-gen u)
  (operation nonce-test (displaced 1 2 init 3) u (0 2) (enc u k))
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k)) (recv (invk u)) (send u)))
  (label 2)
  (parent 1)
  (realized)
  (shape)
  (maps ((0) ((u u) (k k))))
  (origs)
  (ugens (u (1 0))))

(defskeleton uniq-gen-example
  (vars (k k-0 skey) (u akey))
  (defstrand resp 3 (k k) (u (invk u)))
  (defstrand init 1 (k k) (u (invk u)))
  (defstrand resp 2 (k k-0) (u u))
  (precedes ((1 0) (0 0)) ((1 0) (2 0)) ((2 1) (0 2)))
  (non-orig k k-0)
  (uniq-gen (invk u))
  (operation nonce-test (added-strand resp 2) (invk u) (0 2)
    (enc (invk u) k))
  (traces ((recv (enc (invk u) k)) (send u) (recv (invk u)))
    ((send (enc (invk u) k))) ((recv (enc u k-0)) (send (invk u))))
  (label 3)
  (parent 1)
  (unrealized (2 0))
  (dead)
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
  (label 4)
  (unrealized (0 0))
  (origs)
  (ugens)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton uniq-gen-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 1 (k k) (u u))
  (precedes ((1 0) (0 0)))
  (non-orig k)
  (uniq-gen u (invk u))
  (operation encryption-test (added-strand init 1) (enc u k) (0 0))
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k))))
  (label 5)
  (parent 4)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton uniq-gen-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 3 (k k) (u u))
  (precedes ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig k)
  (uniq-gen u (invk u))
  (operation nonce-test (displaced 1 2 init 3) u (0 2) (enc u k))
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k)) (recv (invk u)) (send u)))
  (label 6)
  (parent 5)
  (unrealized (1 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton uniq-gen-example
  (vars (k k-0 skey) (u akey))
  (defstrand resp 3 (k k) (u (invk u)))
  (defstrand init 1 (k k) (u (invk u)))
  (defstrand resp 2 (k k-0) (u u))
  (precedes ((1 0) (0 0)) ((1 0) (2 0)) ((2 1) (0 2)))
  (non-orig k k-0)
  (uniq-gen u (invk u))
  (operation nonce-test (added-strand resp 2) (invk u) (0 2)
    (enc (invk u) k))
  (traces ((recv (enc (invk u) k)) (send u) (recv (invk u)))
    ((send (enc (invk u) k))) ((recv (enc u k-0)) (send (invk u))))
  (label 7)
  (parent 5)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton uniq-gen-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 3 (k k) (u u))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig k)
  (uniq-gen u (invk u))
  (operation nonce-test (displaced 2 0 resp 2) (invk u) (1 1))
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k)) (recv (invk u)) (send u)))
  (label 8)
  (parent 6)
  (realized)
  (shape)
  (maps ((0) ((u u) (k k))))
  (origs)
  (ugens (u (1 0)) ((invk u) (1 0))))

(defskeleton uniq-gen-example
  (vars (k k-0 skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 3 (k k) (u u))
  (defstrand resp 2 (k k-0) (u u))
  (precedes ((1 0) (0 0)) ((1 0) (2 0)) ((1 2) (0 2)) ((2 1) (1 1)))
  (non-orig k k-0)
  (uniq-gen u (invk u))
  (operation nonce-test (added-strand resp 2) (invk u) (1 1))
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k)) (recv (invk u)) (send u))
    ((recv (enc u k-0)) (send (invk u))))
  (label 9)
  (parent 6)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton uniq-gen-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 3 (k k) (u u))
  (defstrand resp 2 (k k) (u u))
  (precedes ((1 0) (0 0)) ((1 0) (2 0)) ((1 2) (0 2)) ((2 1) (1 1)))
  (non-orig k)
  (uniq-gen u (invk u))
  (operation encryption-test (displaced 3 1 init 1) (enc u k-0) (2 0))
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k)) (recv (invk u)) (send u))
    ((recv (enc u k)) (send (invk u))))
  (label 10)
  (parent 9)
  (realized)
  (shape)
  (maps ((0) ((u u) (k k))))
  (origs)
  (ugens (u (1 0)) ((invk u) (1 0))))

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
  (label 11)
  (unrealized (0 0))
  (origs)
  (ugens)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton uniq-orig-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 1 (k k) (u u))
  (precedes ((1 0) (0 0)))
  (non-orig k)
  (uniq-orig u)
  (operation encryption-test (added-strand init 1) (enc u k) (0 0))
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k))))
  (label 12)
  (parent 11)
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
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k)) (recv (invk u)) (send u)))
  (label 13)
  (parent 12)
  (realized)
  (shape)
  (maps ((0) ((u u) (k k))))
  (origs (u (1 0)))
  (ugens))

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
  (label 14)
  (unrealized (0 0))
  (origs ((invk u) (0 1)))
  (ugens)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton uniq-orig-example
  (vars (k skey) (u akey))
  (defstrand resp 3 (k k) (u u))
  (defstrand init 1 (k k) (u u))
  (precedes ((1 0) (0 0)))
  (non-orig k)
  (uniq-orig u (invk u))
  (operation encryption-test (added-strand init 1) (enc u k) (0 0))
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k))))
  (label 15)
  (parent 14)
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
  (traces ((recv (enc u k)) (send (invk u)) (recv u))
    ((send (enc u k)) (recv (invk u)) (send u)))
  (label 16)
  (parent 15)
  (realized)
  (shape)
  (maps ((0) ((u u) (k k))))
  (origs (u (1 0)) ((invk u) (0 1)))
  (ugens))

(comment "Nothing left to do")
