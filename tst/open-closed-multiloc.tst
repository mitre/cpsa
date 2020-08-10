(herald open-closed (bound 44))

(comment "CPSA 4.3.0")
(comment "All input read from tst/open-closed-multiloc.scm")
(comment "Strand count bounded at 44")

(defprotocol open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (load ls old1) (stor ls (cat "st" d o))
      (stor lk (cat "st-k" d o k)) (send (enc "up" k)))
    (auth start-ch))
  (defrole owner-power-dev
    (vars (k skey) (d o name) (start-ch chan))
    (trace (send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    (conf start-ch))
  (defrole owner-open
    (vars (k skey) (n text) (d o name))
    (trace (send (enc "open" d o n k)) (recv n)))
  (defrole owner-close
    (vars (k skey) (n text) (d o name))
    (trace (send (enc "close" d o n k)) (recv n)))
  (defrole dev-open
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "open" d o n k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o o)) (send n)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "close" d o n k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o)) (send n)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat "st" d o o)) (send (enc "you may pass" n k)))
    (uniq-orig n))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule trRl_dev-up-at-4
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 4))))
  (defrule trRl_dev-up-at-3
    (forall ((z strd)) (implies (p "dev-up" z 4) (trans z 3))))
  (defrule trRl_dev-up-at-2
    (forall ((z strd)) (implies (p "dev-up" z 3) (trans z 2))))
  (defrule trRl_dev-up-at-1
    (forall ((z strd)) (implies (p "dev-up" z 2) (trans z 1))))
  (defrule trRl_dev-open-at-3
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 3))))
  (defrule trRl_dev-open-at-2
    (forall ((z strd)) (implies (p "dev-open" z 3) (trans z 2))))
  (defrule trRl_dev-close-at-3
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 3))))
  (defrule trRl_dev-close-at-2
    (forall ((z strd)) (implies (p "dev-close" z 3) (trans z 2))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 2) (p "dev-up" z2 2) (p "dev-up" "k" z1 k)
          (p "dev-up" "k" z2 k))
        (= z1 z2))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d o o)))))
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z 1) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z (cat o o)))
        (gen-st (cat "st" d o o)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton open-closed
  (vars (d o name) (k skey) (start-ch chan))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (deflistener k)
  (uniq-orig k)
  (conf start-ch)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv k) (send k)))
  (label 0)
  (unrealized (0 1) (1 0))
  (preskeleton)
  (origs (k (0 0)))
  (comment "Not a skeleton"))

(defskeleton open-closed
  (vars (d o name) (k skey) (start-ch chan))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (deflistener k)
  (precedes ((0 0) (1 0)))
  (uniq-orig k)
  (conf start-ch)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv k) (send k)))
  (label 1)
  (parent 0)
  (unrealized (0 1) (1 0))
  (origs (k (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton open-closed
  (vars (old old1 mesg) (d o name) (k skey) (start-ch chan)
    (lk ls locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (deflistener k)
  (defstrand dev-up 5 (old old) (old1 old1) (d d) (o o) (k k)
    (start-ch start-ch) (lk lk) (ls ls))
  (precedes ((0 0) (2 0)) ((2 4) (1 0)))
  (uniq-orig k)
  (conf start-ch)
  (auth start-ch)
  (facts (trans 2 1) (trans 2 2) (trans 2 3) (trans 2 4))
  (rule trRl_dev-up-at-1 trRl_dev-up-at-2 trRl_dev-up-at-3
    trRl_dev-up-at-4)
  (operation nonce-test (added-strand dev-up 5) k (1 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv k) (send k))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt old))
      (load ls (cat pt-0 old1)) (stor ls (cat pt-1 "st" d o))
      (stor lk (cat pt-2 "st-k" d o k))))
  (label 2)
  (parent 1)
  (unrealized (0 1) (1 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (load ls old1) (stor ls (cat "st" d o))
      (stor lk (cat "st-k" d o k)) (send (enc "up" k)))
    (auth start-ch))
  (defrole owner-power-dev
    (vars (k skey) (d o name) (start-ch chan))
    (trace (send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    (conf start-ch))
  (defrole owner-open
    (vars (k skey) (n text) (d o name))
    (trace (send (enc "open" d o n k)) (recv n)))
  (defrole owner-close
    (vars (k skey) (n text) (d o name))
    (trace (send (enc "close" d o n k)) (recv n)))
  (defrole dev-open
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "open" d o n k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o o)) (send n)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "close" d o n k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o)) (send n)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat "st" d o o)) (send (enc "you may pass" n k)))
    (uniq-orig n))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule trRl_dev-up-at-4
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 4))))
  (defrule trRl_dev-up-at-3
    (forall ((z strd)) (implies (p "dev-up" z 4) (trans z 3))))
  (defrule trRl_dev-up-at-2
    (forall ((z strd)) (implies (p "dev-up" z 3) (trans z 2))))
  (defrule trRl_dev-up-at-1
    (forall ((z strd)) (implies (p "dev-up" z 2) (trans z 1))))
  (defrule trRl_dev-open-at-3
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 3))))
  (defrule trRl_dev-open-at-2
    (forall ((z strd)) (implies (p "dev-open" z 3) (trans z 2))))
  (defrule trRl_dev-close-at-3
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 3))))
  (defrule trRl_dev-close-at-2
    (forall ((z strd)) (implies (p "dev-close" z 3) (trans z 2))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 2) (p "dev-up" z2 2) (p "dev-up" "k" z1 k)
          (p "dev-up" "k" z2 k))
        (= z1 z2))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d o o)))))
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z 1) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z (cat o o)))
        (gen-st (cat "st" d o o)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton open-closed
  (vars (n text) (d o name) (k skey) (lk ls locn))
  (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk) (ls ls))
  (uniq-orig n)
  (traces
    ((load lk (cat pt "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d o o)) (send (enc "you may pass" n k))))
  (label 3)
  (unrealized)
  (origs (n (0 3)))
  (comment "Not closed under rules"))

(defskeleton open-closed
  (vars (n text) (d o name) (k skey) (lk ls locn))
  (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk) (ls ls))
  (uniq-orig n)
  (genStV (cat "st" d o o))
  (rule gen-state-pass)
  (traces
    ((load lk (cat pt "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d o o)) (send (enc "you may pass" n k))))
  (label 4)
  (parent 3)
  (unrealized (0 2))
  (origs (n (0 3)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton open-closed
  (vars (any mesg) (n n-0 text) (d o name) (k k-0 skey)
    (lk ls lk-0 locn))
  (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (n n-0) (d d) (o o) (k k-0) (lk lk-0)
    (ls ls))
  (precedes ((1 3) (0 2)))
  (uniq-orig n)
  (genStV (cat "st" d o o))
  (facts (trans 1 2) (trans 1 3))
  (rule trRl_dev-open-at-2 trRl_dev-open-at-3)
  (operation channel-test (added-strand dev-open 4)
    (ch-msg ls (cat pt-0 "st" d o o)) (0 2))
  (traces
    ((load lk (cat pt "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d o o)) (send (enc "you may pass" n k)))
    ((load lk-0 (cat pt-1 "st-k" d o k-0))
      (recv (enc "open" d o n-0 k-0)) (load ls (cat pt-2 "st" d any))
      (stor ls (cat pt-0 "st" d o o))))
  (label 5)
  (parent 4)
  (unrealized)
  (shape)
  (maps
    ((0) ((k k) (n n) (d d) (o o) (lk lk) (ls ls) (pt pt) (pt-0 pt-0))))
  (origs (pt-0 (1 3)) (n (0 3))))

(comment "Nothing left to do")

(defprotocol open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (load ls old1) (stor ls (cat "st" d o))
      (stor lk (cat "st-k" d o k)) (send (enc "up" k)))
    (auth start-ch))
  (defrole owner-power-dev
    (vars (k skey) (d o name) (start-ch chan))
    (trace (send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    (conf start-ch))
  (defrole owner-open
    (vars (k skey) (n text) (d o name))
    (trace (send (enc "open" d o n k)) (recv n)))
  (defrole owner-close
    (vars (k skey) (n text) (d o name))
    (trace (send (enc "close" d o n k)) (recv n)))
  (defrole dev-open
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "open" d o n k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o o)) (send n)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "close" d o n k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o)) (send n)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat "st" d o o)) (send (enc "you may pass" n k)))
    (uniq-orig n))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule trRl_dev-up-at-4
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 4))))
  (defrule trRl_dev-up-at-3
    (forall ((z strd)) (implies (p "dev-up" z 4) (trans z 3))))
  (defrule trRl_dev-up-at-2
    (forall ((z strd)) (implies (p "dev-up" z 3) (trans z 2))))
  (defrule trRl_dev-up-at-1
    (forall ((z strd)) (implies (p "dev-up" z 2) (trans z 1))))
  (defrule trRl_dev-open-at-3
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 3))))
  (defrule trRl_dev-open-at-2
    (forall ((z strd)) (implies (p "dev-open" z 3) (trans z 2))))
  (defrule trRl_dev-close-at-3
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 3))))
  (defrule trRl_dev-close-at-2
    (forall ((z strd)) (implies (p "dev-close" z 3) (trans z 2))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 2) (p "dev-up" z2 2) (p "dev-up" "k" z1 k)
          (p "dev-up" "k" z2 k))
        (= z1 z2))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d o o)))))
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z 1) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z (cat o o)))
        (gen-st (cat "st" d o o)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton open-closed
  (vars (n text) (d o d-0 o-0 name) (k skey) (start-ch chan)
    (lk ls locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (defstrand dev-pass 4 (n n) (d d-0) (o o-0) (k k) (lk lk) (ls ls))
  (uniq-orig n k)
  (conf start-ch)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt "st-k" d-0 o-0 k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0))
      (send (enc "you may pass" n k))))
  (label 6)
  (unrealized (0 1) (1 0) (1 1))
  (preskeleton)
  (origs (n (1 3)) (k (0 0)))
  (comment "Not a skeleton"))

(defskeleton open-closed
  (vars (n text) (d o d-0 o-0 name) (k skey) (start-ch chan)
    (lk ls locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (defstrand dev-pass 4 (n n) (d d-0) (o o-0) (k k) (lk lk) (ls ls))
  (precedes ((0 0) (1 0)))
  (uniq-orig n k)
  (conf start-ch)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt "st-k" d-0 o-0 k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0))
      (send (enc "you may pass" n k))))
  (label 7)
  (parent 6)
  (unrealized (0 1) (1 0) (1 1))
  (origs (n (1 3)) (k (0 0)))
  (comment "Not closed under rules"))

(defskeleton open-closed
  (vars (n text) (d o d-0 o-0 name) (k skey) (start-ch chan)
    (lk ls locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (defstrand dev-pass 4 (n n) (d d-0) (o o-0) (k k) (lk lk) (ls ls))
  (precedes ((0 0) (1 0)))
  (uniq-orig n k)
  (genStV (cat "st" d-0 o-0 o-0))
  (conf start-ch)
  (rule gen-state-pass)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt "st-k" d-0 o-0 k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0))
      (send (enc "you may pass" n k))))
  (label 8)
  (parent 7)
  (unrealized (0 1) (1 0) (1 1) (1 2))
  (origs (n (1 3)) (k (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton open-closed
  (vars (old old1 mesg) (n text) (d o d-0 o-0 name) (k skey)
    (start-ch chan) (lk ls lk-0 ls-0 locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (defstrand dev-pass 4 (n n) (d d-0) (o o-0) (k k) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (d d) (o o) (k k)
    (start-ch start-ch) (lk lk-0) (ls ls-0))
  (precedes ((0 0) (2 0)) ((2 4) (1 0)))
  (uniq-orig n k)
  (genStV (cat "st" d-0 o-0 o-0))
  (conf start-ch)
  (auth start-ch)
  (facts (trans 2 1) (trans 2 2) (trans 2 3) (trans 2 4))
  (rule trRl_dev-up-at-1 trRl_dev-up-at-2 trRl_dev-up-at-3
    trRl_dev-up-at-4)
  (operation nonce-test (added-strand dev-up 5) k (1 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt "st-k" d-0 o-0 k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0))
      (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk-0 (cat pt-1 old))
      (load ls-0 (cat pt-2 old1)) (stor ls-0 (cat pt-3 "st" d o))
      (stor lk-0 (cat pt-4 "st-k" d o k))))
  (label 9)
  (parent 8)
  (unrealized (0 1) (1 0) (1 1) (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton open-closed
  (vars (old old1 mesg) (n text) (d o name) (k skey) (start-ch chan)
    (ls lk ls-0 locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (d d) (o o) (k k)
    (start-ch start-ch) (lk lk) (ls ls-0))
  (precedes ((0 0) (2 0)) ((2 4) (1 0)))
  (uniq-orig n k)
  (genStV (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (trans 2 1) (trans 2 2) (trans 2 3) (trans 2 4))
  (operation nonce-test
    (contracted (d-0 d) (o-0 o) (lk-0 lk) (pt-4 pt-3)) k (1 0)
    (ch-msg start-ch (cat "power-up" d o k))
    (ch-msg lk (cat pt-3 "st-k" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-3 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls-0 (cat pt-1 old1)) (stor ls-0 (cat pt-2 "st" d o))
      (stor lk (cat pt-3 "st-k" d o k))))
  (label 10)
  (parent 9)
  (unrealized (0 1) (1 1) (1 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton open-closed
  (vars (old old1 mesg) (n text) (d o name) (k skey) (start-ch chan)
    (ls lk ls-0 locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (d d) (o o) (k k)
    (start-ch start-ch) (lk lk) (ls ls-0))
  (defstrand user-pass 1 (k k))
  (precedes ((0 0) (2 0)) ((2 4) (1 0)) ((3 0) (1 1)))
  (uniq-orig n k)
  (genStV (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (trans 2 1) (trans 2 2) (trans 2 3) (trans 2 4))
  (operation encryption-test (added-strand user-pass 1)
    (enc "may I pass" k) (1 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-3 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls-0 (cat pt-1 old1)) (stor ls-0 (cat pt-2 "st" d o))
      (stor lk (cat pt-3 "st-k" d o k))) ((send (enc "may I pass" k))))
  (label 11)
  (parent 10)
  (unrealized (0 1) (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton open-closed
  (vars (old old1 mesg) (n text) (d o name) (k skey) (start-ch chan)
    (ls lk ls-0 locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (d d) (o o) (k k)
    (start-ch start-ch) (lk lk) (ls ls-0))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((0 0) (3 0)) ((2 4) (1 0)) ((3 1) (1 1)))
  (uniq-orig n k)
  (genStV (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (trans 2 1) (trans 2 2) (trans 2 3) (trans 2 4))
  (operation encryption-test (added-listener k) (enc "may I pass" k)
    (1 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-3 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls-0 (cat pt-1 old1)) (stor ls-0 (cat pt-2 "st" d o))
      (stor lk (cat pt-3 "st-k" d o k))) ((recv k) (send k)))
  (label 12)
  (parent 10)
  (seen 14)
  (unrealized (0 1) (1 2) (3 0))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton open-closed
  (vars (old old1 any mesg) (n n-0 text) (d o name) (k k-0 skey)
    (start-ch chan) (ls lk ls-0 lk-0 locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (d d) (o o) (k k)
    (start-ch start-ch) (lk lk) (ls ls-0))
  (defstrand user-pass 1 (k k))
  (defstrand dev-open 4 (any any) (n n-0) (d d) (o o) (k k-0) (lk lk-0)
    (ls ls))
  (precedes ((0 0) (2 0)) ((2 4) (1 0)) ((3 0) (1 1)) ((4 3) (1 2)))
  (uniq-orig n k)
  (genStV (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (trans 4 2) (trans 4 3) (trans 2 1) (trans 2 2) (trans 2 3)
    (trans 2 4))
  (rule trRl_dev-open-at-2 trRl_dev-open-at-3)
  (operation channel-test (added-strand dev-open 4)
    (ch-msg ls (cat pt "st" d o o)) (1 2))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-3 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls-0 (cat pt-1 old1)) (stor ls-0 (cat pt-2 "st" d o))
      (stor lk (cat pt-3 "st-k" d o k))) ((send (enc "may I pass" k)))
    ((load lk-0 (cat pt-4 "st-k" d o k-0))
      (recv (enc "open" d o n-0 k-0)) (load ls (cat pt-5 "st" d any))
      (stor ls (cat pt "st" d o o))))
  (label 13)
  (parent 11)
  (seen 15)
  (unrealized (0 1))
  (comment "3 in cohort - 2 not yet seen"))

(defskeleton open-closed
  (vars (old old1 mesg) (n text) (d o name) (k skey) (start-ch chan)
    (ls lk ls-0 locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (d d) (o o) (k k)
    (start-ch start-ch) (lk lk) (ls ls-0))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 4) (1 0)) ((2 4) (3 0)) ((3 1) (1 1)))
  (uniq-orig n k)
  (genStV (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (trans 2 1) (trans 2 2) (trans 2 3) (trans 2 4))
  (operation nonce-test (displaced 4 2 dev-up 5) k (3 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-3 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls-0 (cat pt-1 old1)) (stor ls-0 (cat pt-2 "st" d o))
      (stor lk (cat pt-3 "st-k" d o k))) ((recv k) (send k)))
  (label 14)
  (parent 12)
  (unrealized (0 1) (1 2) (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton open-closed
  (vars (any old old1 mesg) (n n-0 text) (d o name) (k k-0 skey)
    (start-ch chan) (ls lk lk-0 ls-0 locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk-0) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-open 4 (any any) (n n-0) (d d) (o o) (k k-0) (lk lk)
    (ls ls))
  (defstrand dev-up 6 (old old) (old1 old1) (d d) (o o) (k k)
    (start-ch start-ch) (lk lk-0) (ls ls-0))
  (precedes ((0 0) (4 0)) ((2 0) (1 1)) ((3 3) (1 2)) ((4 4) (1 0))
    ((4 5) (0 1)))
  (uniq-orig n k)
  (genStV (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (trans 3 2) (trans 3 3) (trans 4 1) (trans 4 2) (trans 4 3)
    (trans 4 4))
  (operation encryption-test (displaced 2 5 dev-up 6) (enc "up" k)
    (0 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk-0 (cat pt-5 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((send (enc "may I pass" k)))
    ((load lk (cat pt-0 "st-k" d o k-0)) (recv (enc "open" d o n-0 k-0))
      (load ls (cat pt-1 "st" d any)) (stor ls (cat pt "st" d o o)))
    ((recv start-ch (cat "power-up" d o k)) (load lk-0 (cat pt-2 old))
      (load ls-0 (cat pt-3 old1)) (stor ls-0 (cat pt-4 "st" d o))
      (stor lk-0 (cat pt-5 "st-k" d o k)) (send (enc "up" k))))
  (label 15)
  (parent 13)
  (unrealized)
  (shape)
  (maps
    ((0 1)
      ((k k) (d d) (o o) (start-ch start-ch) (n n) (d-0 d) (o-0 o)
        (lk lk-0) (ls ls) (pt pt-5) (pt-0 pt))))
  (origs (pt-4 (4 3)) (pt-5 (4 4)) (pt (3 3)) (n (1 3)) (k (0 0))))

(defskeleton open-closed
  (vars (old old1 any mesg) (n n-0 text) (d o name) (k k-0 skey)
    (start-ch chan) (ls lk ls-0 lk-0 locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (d d) (o o) (k k)
    (start-ch start-ch) (lk lk) (ls ls-0))
  (defstrand user-pass 1 (k k))
  (defstrand dev-open 4 (any any) (n n-0) (d d) (o o) (k k-0) (lk lk-0)
    (ls ls))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((0 0) (5 0)) ((2 4) (1 0)) ((3 0) (1 1))
    ((4 3) (1 2)) ((5 1) (0 1)))
  (uniq-orig n k)
  (genStV (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (trans 4 2) (trans 4 3) (trans 2 1) (trans 2 2) (trans 2 3)
    (trans 2 4))
  (operation encryption-test (added-listener k) (enc "up" k) (0 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-3 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls-0 (cat pt-1 old1)) (stor ls-0 (cat pt-2 "st" d o))
      (stor lk (cat pt-3 "st-k" d o k))) ((send (enc "may I pass" k)))
    ((load lk-0 (cat pt-4 "st-k" d o k-0))
      (recv (enc "open" d o n-0 k-0)) (load ls (cat pt-5 "st" d any))
      (stor ls (cat pt "st" d o o))) ((recv k) (send k)))
  (label 16)
  (parent 13)
  (seen 17)
  (unrealized (5 0))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton open-closed
  (vars (old old1 any mesg) (n n-0 text) (d o name) (k k-0 skey)
    (start-ch chan) (ls lk ls-0 lk-0 locn))
  (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
  (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (d d) (o o) (k k)
    (start-ch start-ch) (lk lk) (ls ls-0))
  (defstrand user-pass 1 (k k))
  (defstrand dev-open 4 (any any) (n n-0) (d d) (o o) (k k-0) (lk lk-0)
    (ls ls))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 4) (1 0)) ((2 4) (5 0)) ((3 0) (1 1))
    ((4 3) (1 2)) ((5 1) (0 1)))
  (uniq-orig n k)
  (genStV (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (trans 4 2) (trans 4 3) (trans 2 1) (trans 2 2) (trans 2 3)
    (trans 2 4))
  (operation nonce-test (displaced 6 2 dev-up 5) k (5 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-3 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls-0 (cat pt-1 old1)) (stor ls-0 (cat pt-2 "st" d o))
      (stor lk (cat pt-3 "st-k" d o k))) ((send (enc "may I pass" k)))
    ((load lk-0 (cat pt-4 "st-k" d o k-0))
      (recv (enc "open" d o n-0 k-0)) (load ls (cat pt-5 "st" d any))
      (stor ls (cat pt "st" d o o))) ((recv k) (send k)))
  (label 17)
  (parent 16)
  (unrealized (5 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
