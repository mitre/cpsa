(herald auth-enc)

(comment "CPSA 4.4.5")
(comment "All input read from tst/auth-enc.scm")

(defprotocol auth-enc basic
  (defrole init
    (vars (n text) (k skey) (ch chan))
    (trace (send ch (enc n k)) (send ch (cat n k)))
    (uniq-orig k n)
    (inputs ch))
  (defrole resp
    (vars (n text) (k skey) (ch chan))
    (trace (recv ch (enc n k)) (recv ch (cat n k)))
    (inputs ch)
    (outputs n))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton auth-enc
  (vars (k skey) (n text) (ch chan))
  (defstrand resp 2 (k k) (n n) (ch ch))
  (auth ch)
  (traces ((recv ch (enc n k)) (recv ch (cat n k))))
  (label 0)
  (unrealized (0 0) (0 1))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton auth-enc
  (vars (k skey) (n text) (ch chan))
  (defstrand resp 2 (k k) (n n) (ch ch))
  (defstrand init 1 (k k) (n n) (ch ch))
  (precedes ((1 0) (0 0)))
  (uniq-orig n)
  (auth ch)
  (operation channel-test (added-strand init 1) (ch-msg ch (enc n k))
    (0 0))
  (strand-map 0)
  (traces ((recv ch (enc n k)) (recv ch (cat n k)))
    ((send ch (enc n k))))
  (label 1)
  (parent 0)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton auth-enc
  (vars (k skey) (n text) (ch chan))
  (defstrand resp 2 (k k) (n n) (ch ch))
  (defstrand init 2 (k k) (n n) (ch ch))
  (precedes ((1 0) (0 0)) ((1 1) (0 1)))
  (uniq-orig k n)
  (auth ch)
  (operation channel-test (displaced 1 2 init 2) (ch-msg ch (cat n k))
    (0 1))
  (strand-map 0 1)
  (traces ((recv ch (enc n k)) (recv ch (cat n k)))
    ((send ch (enc n k)) (send ch (cat n k))))
  (label 2)
  (parent 1)
  (realized)
  (shape)
  (maps ((0) ((ch ch) (n n) (k k))))
  (origs (n (1 0)) (k (1 1))))

(comment "Nothing left to do")
