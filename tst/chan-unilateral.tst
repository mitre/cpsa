(herald chan-unilateral)

(comment "CPSA 4.2.3")
(comment "All input read from tst/chan-unilateral.scm")

(defprotocol unilateral basic
  (defrole init
    (vars (n text) (ch chan))
    (trace (send ch n) (recv n))
    (uniq-orig n))
  (defrole resp (vars (n text) (ch chan)) (trace (recv ch n) (send n)))
  (comment
    "Unilateral protocol using channels with differing assumptions"))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand init 2 (n n) (ch ch))
  (uniq-orig n)
  (traces ((send ch n) (recv n)))
  (label 0)
  (unrealized)
  (shape)
  (maps ((0) ((ch ch) (n n))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol unilateral basic
  (defrole init
    (vars (n text) (ch chan))
    (trace (send ch n) (recv n))
    (uniq-orig n))
  (defrole resp (vars (n text) (ch chan)) (trace (recv ch n) (send n)))
  (comment
    "Unilateral protocol using channels with differing assumptions"))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand init 2 (n n) (ch ch))
  (uniq-orig n)
  (auth ch)
  (traces ((send ch n) (recv n)))
  (label 1)
  (unrealized)
  (shape)
  (maps ((0) ((ch ch) (n n))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol unilateral basic
  (defrole init
    (vars (n text) (ch chan))
    (trace (send ch n) (recv n))
    (uniq-orig n))
  (defrole resp (vars (n text) (ch chan)) (trace (recv ch n) (send n)))
  (comment
    "Unilateral protocol using channels with differing assumptions"))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand init 2 (n n) (ch ch))
  (uniq-orig n)
  (conf ch)
  (traces ((send ch n) (recv n)))
  (label 2)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand init 2 (n n) (ch ch))
  (defstrand resp 2 (n n) (ch ch))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig n)
  (conf ch)
  (operation nonce-test (added-strand resp 2) n (0 1) (ch-msg ch n))
  (traces ((send ch n) (recv n)) ((recv ch n) (send n)))
  (label 3)
  (parent 2)
  (unrealized)
  (shape)
  (maps ((0) ((ch ch) (n n))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol unilateral basic
  (defrole init
    (vars (n text) (ch chan))
    (trace (send ch n) (recv n))
    (uniq-orig n))
  (defrole resp (vars (n text) (ch chan)) (trace (recv ch n) (send n)))
  (comment
    "Unilateral protocol using channels with differing assumptions"))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand init 2 (n n) (ch ch))
  (uniq-orig n)
  (conf ch)
  (auth ch)
  (traces ((send ch n) (recv n)))
  (label 4)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand init 2 (n n) (ch ch))
  (defstrand resp 2 (n n) (ch ch))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig n)
  (conf ch)
  (auth ch)
  (operation nonce-test (added-strand resp 2) n (0 1) (ch-msg ch n))
  (traces ((send ch n) (recv n)) ((recv ch n) (send n)))
  (label 5)
  (parent 4)
  (unrealized)
  (shape)
  (maps ((0) ((ch ch) (n n))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol unilateral basic
  (defrole init
    (vars (n text) (ch chan))
    (trace (send ch n) (recv n))
    (uniq-orig n))
  (defrole resp (vars (n text) (ch chan)) (trace (recv ch n) (send n)))
  (comment
    "Unilateral protocol using channels with differing assumptions"))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand resp 2 (n n) (ch ch))
  (pen-non-orig n)
  (traces ((recv ch n) (send n)))
  (label 6)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton unilateral
  (vars (n text) (ch ch-0 chan))
  (defstrand resp 2 (n n) (ch ch))
  (defstrand init 1 (n n) (ch ch-0))
  (precedes ((1 0) (0 0)))
  (pen-non-orig n)
  (uniq-orig n)
  (operation nonce-test (added-strand init 1) n (0 0))
  (traces ((recv ch n) (send n)) ((send ch-0 n)))
  (label 7)
  (parent 6)
  (unrealized)
  (shape)
  (maps ((0) ((n n) (ch ch))))
  (origs (n (1 0))))

(comment "Nothing left to do")

(defprotocol unilateral basic
  (defrole init
    (vars (n text) (ch chan))
    (trace (send ch n) (recv n))
    (uniq-orig n))
  (defrole resp (vars (n text) (ch chan)) (trace (recv ch n) (send n)))
  (comment
    "Unilateral protocol using channels with differing assumptions"))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand resp 2 (n n) (ch ch))
  (pen-non-orig n)
  (auth ch)
  (traces ((recv ch n) (send n)))
  (label 8)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand resp 2 (n n) (ch ch))
  (defstrand init 1 (n n) (ch ch))
  (precedes ((1 0) (0 0)))
  (pen-non-orig n)
  (uniq-orig n)
  (auth ch)
  (operation channel-test (added-strand init 1) (ch-msg ch n) (0 0))
  (traces ((recv ch n) (send n)) ((send ch n)))
  (label 9)
  (parent 8)
  (unrealized)
  (shape)
  (maps ((0) ((n n) (ch ch))))
  (origs (n (1 0))))

(comment "Nothing left to do")

(defprotocol unilateral basic
  (defrole init
    (vars (n text) (ch chan))
    (trace (send ch n) (recv n))
    (uniq-orig n))
  (defrole resp (vars (n text) (ch chan)) (trace (recv ch n) (send n)))
  (comment
    "Unilateral protocol using channels with differing assumptions"))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand resp 2 (n n) (ch ch))
  (pen-non-orig n)
  (conf ch)
  (traces ((recv ch n) (send n)))
  (label 10)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton unilateral
  (vars (n text) (ch ch-0 chan))
  (defstrand resp 2 (n n) (ch ch))
  (defstrand init 1 (n n) (ch ch-0))
  (precedes ((1 0) (0 0)))
  (pen-non-orig n)
  (uniq-orig n)
  (conf ch)
  (operation nonce-test (added-strand init 1) n (0 0))
  (traces ((recv ch n) (send n)) ((send ch-0 n)))
  (label 11)
  (parent 10)
  (unrealized)
  (shape)
  (maps ((0) ((n n) (ch ch))))
  (origs (n (1 0))))

(comment "Nothing left to do")

(defprotocol unilateral basic
  (defrole init
    (vars (n text) (ch chan))
    (trace (send ch n) (recv n))
    (uniq-orig n))
  (defrole resp (vars (n text) (ch chan)) (trace (recv ch n) (send n)))
  (comment
    "Unilateral protocol using channels with differing assumptions"))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand resp 2 (n n) (ch ch))
  (pen-non-orig n)
  (conf ch)
  (auth ch)
  (traces ((recv ch n) (send n)))
  (label 12)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand resp 2 (n n) (ch ch))
  (defstrand init 1 (n n) (ch ch))
  (precedes ((1 0) (0 0)))
  (pen-non-orig n)
  (uniq-orig n)
  (conf ch)
  (auth ch)
  (operation channel-test (added-strand init 1) (ch-msg ch n) (0 0))
  (traces ((recv ch n) (send n)) ((send ch n)))
  (label 13)
  (parent 12)
  (unrealized)
  (shape)
  (maps ((0) ((n n) (ch ch))))
  (origs (n (1 0))))

(comment "Nothing left to do")
