(herald disclosure)

(comment "CPSA 4.3.1")
(comment "All input read from tst/disclosure.scm")

(defprotocol disc basic
  (defrole init
    (vars (a b name) (k skey) (n text))
    (trace (send (enc a b n k)) (recv n) (send k))
    (pen-non-orig k))
  (defrole resp
    (vars (a b name) (k skey) (n text))
    (trace (recv (enc a b n k)) (send n)))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton disc
  (vars (k skey) (n text) (a b name))
  (defstrand init 2 (k k) (n n) (a a) (b b))
  (pen-non-orig k)
  (uniq-orig n)
  (traces ((send (enc a b n k)) (recv n)))
  (label 0)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton disc
  (vars (k skey) (n text) (a b name))
  (defstrand init 2 (k k) (n n) (a a) (b b))
  (defstrand resp 2 (k k) (n n) (a a) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (pen-non-orig k)
  (uniq-orig n)
  (operation nonce-test (added-strand resp 2) n (0 1) (enc a b n k))
  (traces ((send (enc a b n k)) (recv n))
    ((recv (enc a b n k)) (send n)))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((n n) (a a) (b b) (k k))))
  (origs (n (0 0))))

(defskeleton disc
  (vars (k skey) (n text) (a b name))
  (defstrand init 2 (k k) (n n) (a a) (b b))
  (deflistener k)
  (precedes ((1 1) (0 1)))
  (pen-non-orig k)
  (uniq-orig n)
  (operation nonce-test (added-listener k) n (0 1) (enc a b n k))
  (traces ((send (enc a b n k)) (recv n)) ((recv k) (send k)))
  (label 2)
  (parent 0)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton disc
  (vars (k skey) (n n-0 text) (a b a-0 b-0 name))
  (defstrand init 2 (k k) (n n) (a a) (b b))
  (deflistener k)
  (defstrand init 3 (k k) (n n-0) (a a-0) (b b-0))
  (precedes ((1 1) (0 1)) ((2 2) (1 0)))
  (pen-non-orig k)
  (uniq-orig n)
  (operation nonce-test (added-strand init 3) k (1 0))
  (traces ((send (enc a b n k)) (recv n)) ((recv k) (send k))
    ((send (enc a-0 b-0 n-0 k)) (recv n-0) (send k)))
  (label 3)
  (parent 2)
  (realized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton disc
  (vars (k skey) (n n-0 text) (a b a-0 b-0 name))
  (defstrand init 2 (k k) (n n) (a a) (b b))
  (defstrand init 3 (k k) (n n-0) (a a-0) (b b-0))
  (precedes ((1 2) (0 1)))
  (pen-non-orig k)
  (uniq-orig n)
  (operation generalization deleted (1 0))
  (traces ((send (enc a b n k)) (recv n))
    ((send (enc a-0 b-0 n-0 k)) (recv n-0) (send k)))
  (label 4)
  (parent 3)
  (realized)
  (shape)
  (maps ((0) ((n n) (a a) (b b) (k k))))
  (origs (n (0 0))))

(comment "Nothing left to do")