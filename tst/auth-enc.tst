(herald auth-enc)

(comment "CPSA 4.2.3")
(comment "All input read from auth-enc.scm")

(defprotocol auth-enc basic
  (defrole init
    (vars (n text) (k skey) (ch chan))
    (trace (send ch (enc n k)) (send ch (cat n k)))
    (uniq-orig n k)
    (inputs ch))
  (defrole resp
    (vars (n text) (k skey) (ch chan))
    (trace (recv ch (enc n k)) (recv ch (cat n k)))
    (inputs ch)
    (outputs n)))

(defskeleton auth-enc
  (vars (n text) (k skey) (ch chan))
  (defstrand resp 2 (n n) (k k) (ch ch))
  (auth ch)
  (traces ((recv ch (enc n k)) (recv ch (cat n k))))
  (label 0)
  (unrealized (0 0) (0 1))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton auth-enc
  (vars (n text) (k skey) (ch chan))
  (defstrand resp 2 (n n) (k k) (ch ch))
  (defstrand init 1 (n n) (k k) (ch ch))
  (precedes ((1 0) (0 0)))
  (uniq-orig n)
  (auth ch)
  (operation channel-test (added-strand init 1) (ch-msg ch (enc n k))
    (0 0))
  (traces ((recv ch (enc n k)) (recv ch (cat n k)))
    ((send ch (enc n k))))
  (label 1)
  (parent 0)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton auth-enc
  (vars (n text) (k skey) (ch chan))
  (defstrand resp 2 (n n) (k k) (ch ch))
  (defstrand init 2 (n n) (k k) (ch ch))
  (precedes ((1 0) (0 0)) ((1 1) (0 1)))
  (uniq-orig n k)
  (auth ch)
  (operation channel-test (displaced 1 2 init 2) (ch-msg ch (cat n k))
    (0 1))
  (traces ((recv ch (enc n k)) (recv ch (cat n k)))
    ((send ch (enc n k)) (send ch (cat n k))))
  (label 2)
  (parent 1)
  (unrealized)
  (shape)
  (maps ((0) ((ch ch) (n n) (k k))))
  (origs (n (1 0)) (k (1 1))))

(comment "Nothing left to do")
