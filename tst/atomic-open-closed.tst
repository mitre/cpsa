(herald atomic-open-closed (bound 44))

(comment "CPSA 4.4.3")
(comment "All input read from tst/atomic-open-closed.scm")
(comment "Strand count bounded at 44")

(defprotocol atomic-open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (stor lk (cat "st-k" d o k)) (load ls old1)
      (stor ls (cat "st" d o)) (send (enc "up" k)))
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
    (trace (recv (enc "open" d o n k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o o)) (send n)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (recv (enc "close" d o n k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o)) (send n)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (recv (enc "may I pass" k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d o o)) (send (enc "you may pass" n k)))
    (uniq-orig n))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z (idx 1)) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z (cat o o)))
        (gen-st (cat "st" d o o)))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d o o)))))
  (defrule gen-state-open
    (forall ((z strd) (d o k mesg))
      (implies
        (and (p "dev-open" "d" z d) (p "dev-open" "o" z o)
          (p "dev-open" "k" z k))
        (gen-st (cat "st-k" d o k)))))
  (defrule gen-state-close
    (forall ((z strd) (d o k mesg))
      (implies
        (and (p "dev-close" "d" z d) (p "dev-close" "o" z o)
          (p "dev-close" "k" z k))
        (gen-st (cat "st-k" d o k)))))
  (defrule gen-state-pass
    (forall ((z strd) (d o k mesg))
      (implies
        (and (p "dev-pass" "d" z d) (p "dev-pass" "o" z o)
          (p "dev-pass" "k" z k))
        (gen-st (cat "st-k" d o k)))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 (idx 2)) (p "dev-up" z2 (idx 2))
          (p "dev-up" "k" z1 k) (p "dev-up" "k" z2 k))
        (= z1 z2))))
  (defrule intro-same-dev-up
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-up" "lk" z lk) (p "dev-up" "ls" z ls))
        (fact same-dev ls lk))))
  (defrule intro-same-dev-open
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-open" "lk" z lk) (p "dev-open" "ls" z ls))
        (fact same-dev ls lk))))
  (defrule intro-same-dev-close
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-close" "lk" z lk) (p "dev-close" "ls" z ls))
        (fact same-dev ls lk))))
  (defrule intro-same-dev-pass
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-pass" "lk" z lk) (p "dev-pass" "ls" z ls))
        (fact same-dev ls lk))))
  (defrule same-dev-ls-lk
    (forall ((ls lk lk-0 locn))
      (implies
        (and (fact same-dev ls lk) (fact same-dev ls lk-0))
        (= lk lk-0))))
  (defrule same-dev-lk-ls
    (forall ((lk ls ls-0 locn))
      (implies
        (and (fact same-dev ls lk) (fact same-dev ls-0 lk))
        (= ls ls-0))))
  (defrule single-thread-up-up
    (forall ((x y strd) (lk locn))
      (implies
        (and (p "dev-up" x (idx 5)) (p "dev-up" y (idx 5))
          (p "dev-up" "lk" x lk) (p "dev-up" "lk" y lk))
        (or
          (= x y)
          (prec x (idx 4) y (idx 1))
          (prec y (idx 4) x (idx 1))))))
  (defrule single-thread-up-open
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-up" x (idx 5)) (p "dev-open" y (idx 4))
          (p "dev-up" "ls" x ls) (p "dev-open" "ls" y ls))
        (or (prec x (idx 4) y (idx 1)) (prec y (idx 3) x (idx 1))))))
  (defrule single-thread-up-close
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-up" x (idx 5)) (p "dev-close" y (idx 4))
          (p "dev-up" "ls" x ls) (p "dev-close" "ls" y ls))
        (or (prec x (idx 4) y (idx 1)) (prec y (idx 3) x (idx 1))))))
  (defrule single-thread-open-open
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-open" x (idx 4)) (p "dev-open" y (idx 4))
          (p "dev-open" "ls" x ls) (p "dev-open" "ls" y ls))
        (or
          (= x y)
          (prec x (idx 3) y (idx 1))
          (prec y (idx 3) x (idx 1))))))
  (defrule single-thread-ls-open-close
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-open" x (idx 4)) (p "dev-close" y (idx 4))
          (p "dev-open" "ls" x ls) (p "dev-close" "ls" y ls))
        (or (prec x (idx 3) y (idx 1)) (prec y (idx 3) x (idx 1))))))
  (defrule single-thread-close-close
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-close" x (idx 4)) (p "dev-close" y (idx 4))
          (p "dev-close" "ls" x ls) (p "dev-close" "ls" y ls))
        (or
          (= x y)
          (prec x (idx 3) y (idx 1))
          (prec y (idx 3) x (idx 1))))))
  (defrule atomic-up-pass
    (forall ((x y strd) (lk locn))
      (implies
        (and (p "dev-up" x (idx 5)) (p "dev-pass" y (idx 3))
          (p "dev-up" "lk" x lk) (p "dev-pass" "lk" y lk)
          (prec x (idx 2) y (idx 1)))
        (prec x (idx 4) y (idx 1)))))
  (defrule dev-up-completes
    (forall ((x strd))
      (implies (p "dev-up" x (idx 2)) (p "dev-up" x (idx 5)))))
  (defrule dev-open-completes
    (forall ((x strd))
      (implies (p "dev-open" x (idx 2)) (p "dev-open" x (idx 4)))))
  (defrule dev-close-completes
    (forall ((x strd))
      (implies (p "dev-close" x (idx 2)) (p "dev-close" x (idx 4)))))
  (defrule dev-pass-completes
    (forall ((x strd))
      (implies (p "dev-pass" x (idx 2)) (p "dev-pass" x (idx 3)))))
  (defrule dev-up-atomic1
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-up" z (idx 5)) (prec x i1 z (idx 4)))
        (or (= x z) (prec x i1 z (idx 1))))))
  (defrule dev-up-atomic2
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-up" z (idx 5)) (prec z (idx 1) x i1))
        (or (= x z) (prec z (idx 4) x i1)))))
  (defrule dev-open-atomic1
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-open" z (idx 4)) (prec x i1 z (idx 3)))
        (or (= x z) (prec x i1 z (idx 1))))))
  (defrule dev-open-atomic2
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-open" z (idx 4)) (prec z (idx 1) x i1))
        (or (= x z) (prec z (idx 3) x i1)))))
  (defrule dev-close-atomic1
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-close" z (idx 4)) (prec x i1 z (idx 3)))
        (or (= x z) (prec x i1 z (idx 1))))))
  (defrule dev-close-atomic2
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-close" z (idx 4)) (prec z (idx 1) x i1))
        (or (= x z) (prec z (idx 3) x i1)))))
  (defrule dev-pass-atomic1
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-pass" z (idx 3)) (prec x i1 z (idx 2)))
        (or (= x z) (prec x i1 z (idx 1))))))
  (defrule dev-pass-atomic2
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-pass" z (idx 3)) (prec z (idx 1) x i1))
        (or (= x z) (prec z (idx 2) x i1)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule trRl_dev-up-at-4
    (forall ((z strd))
      (implies (p "dev-up" z (idx 5)) (trans z (idx 4)))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd))
      (implies (p "dev-up" z (idx 5)) (trans z (idx 3)))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd))
      (implies (p "dev-up" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd))
      (implies (p "dev-up" z (idx 3)) (trans z (idx 1)))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-open-at-2
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 2)))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd))
      (implies (p "dev-close" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd))
      (implies (p "dev-close" z (idx 4)) (trans z (idx 2)))))
  (defgenrule cau-dev-open-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-open" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-close-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-close" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-pass-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-pass" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1)))))))

(defskeleton atomic-open-closed
  (vars (k skey) (d o name) (start-ch chan))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
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

(defskeleton atomic-open-closed
  (vars (k skey) (d o name) (start-ch chan))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
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

(defskeleton atomic-open-closed
  (vars (old old1 mesg) (k skey) (d o name) (pt pt-0 pt-1 pt-2 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (deflistener k)
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (precedes ((0 0) (2 0)) ((2 4) (1 0)))
  (uniq-orig k)
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (rule dev-up-atomic2 dev-up-completes intro-same-dev-up
    trRl_dev-up-at-1 trRl_dev-up-at-2 trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation nonce-test (added-strand dev-up 3) k (1 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv k) (send k))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt old))
      (stor lk (cat pt-0 "st-k" d o k)) (load ls (cat pt-1 old1))
      (stor ls (cat pt-2 "st" d o))))
  (label 2)
  (parent 1)
  (seen 2)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol atomic-open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (stor lk (cat "st-k" d o k)) (load ls old1)
      (stor ls (cat "st" d o)) (send (enc "up" k)))
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
    (trace (recv (enc "open" d o n k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o o)) (send n)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (recv (enc "close" d o n k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o)) (send n)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (recv (enc "may I pass" k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d o o)) (send (enc "you may pass" n k)))
    (uniq-orig n))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z (idx 1)) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z (cat o o)))
        (gen-st (cat "st" d o o)))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d o o)))))
  (defrule gen-state-open
    (forall ((z strd) (d o k mesg))
      (implies
        (and (p "dev-open" "d" z d) (p "dev-open" "o" z o)
          (p "dev-open" "k" z k))
        (gen-st (cat "st-k" d o k)))))
  (defrule gen-state-close
    (forall ((z strd) (d o k mesg))
      (implies
        (and (p "dev-close" "d" z d) (p "dev-close" "o" z o)
          (p "dev-close" "k" z k))
        (gen-st (cat "st-k" d o k)))))
  (defrule gen-state-pass
    (forall ((z strd) (d o k mesg))
      (implies
        (and (p "dev-pass" "d" z d) (p "dev-pass" "o" z o)
          (p "dev-pass" "k" z k))
        (gen-st (cat "st-k" d o k)))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 (idx 2)) (p "dev-up" z2 (idx 2))
          (p "dev-up" "k" z1 k) (p "dev-up" "k" z2 k))
        (= z1 z2))))
  (defrule intro-same-dev-up
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-up" "lk" z lk) (p "dev-up" "ls" z ls))
        (fact same-dev ls lk))))
  (defrule intro-same-dev-open
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-open" "lk" z lk) (p "dev-open" "ls" z ls))
        (fact same-dev ls lk))))
  (defrule intro-same-dev-close
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-close" "lk" z lk) (p "dev-close" "ls" z ls))
        (fact same-dev ls lk))))
  (defrule intro-same-dev-pass
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-pass" "lk" z lk) (p "dev-pass" "ls" z ls))
        (fact same-dev ls lk))))
  (defrule same-dev-ls-lk
    (forall ((ls lk lk-0 locn))
      (implies
        (and (fact same-dev ls lk) (fact same-dev ls lk-0))
        (= lk lk-0))))
  (defrule same-dev-lk-ls
    (forall ((lk ls ls-0 locn))
      (implies
        (and (fact same-dev ls lk) (fact same-dev ls-0 lk))
        (= ls ls-0))))
  (defrule single-thread-up-up
    (forall ((x y strd) (lk locn))
      (implies
        (and (p "dev-up" x (idx 5)) (p "dev-up" y (idx 5))
          (p "dev-up" "lk" x lk) (p "dev-up" "lk" y lk))
        (or
          (= x y)
          (prec x (idx 4) y (idx 1))
          (prec y (idx 4) x (idx 1))))))
  (defrule single-thread-up-open
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-up" x (idx 5)) (p "dev-open" y (idx 4))
          (p "dev-up" "ls" x ls) (p "dev-open" "ls" y ls))
        (or (prec x (idx 4) y (idx 1)) (prec y (idx 3) x (idx 1))))))
  (defrule single-thread-up-close
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-up" x (idx 5)) (p "dev-close" y (idx 4))
          (p "dev-up" "ls" x ls) (p "dev-close" "ls" y ls))
        (or (prec x (idx 4) y (idx 1)) (prec y (idx 3) x (idx 1))))))
  (defrule single-thread-open-open
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-open" x (idx 4)) (p "dev-open" y (idx 4))
          (p "dev-open" "ls" x ls) (p "dev-open" "ls" y ls))
        (or
          (= x y)
          (prec x (idx 3) y (idx 1))
          (prec y (idx 3) x (idx 1))))))
  (defrule single-thread-ls-open-close
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-open" x (idx 4)) (p "dev-close" y (idx 4))
          (p "dev-open" "ls" x ls) (p "dev-close" "ls" y ls))
        (or (prec x (idx 3) y (idx 1)) (prec y (idx 3) x (idx 1))))))
  (defrule single-thread-close-close
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-close" x (idx 4)) (p "dev-close" y (idx 4))
          (p "dev-close" "ls" x ls) (p "dev-close" "ls" y ls))
        (or
          (= x y)
          (prec x (idx 3) y (idx 1))
          (prec y (idx 3) x (idx 1))))))
  (defrule atomic-up-pass
    (forall ((x y strd) (lk locn))
      (implies
        (and (p "dev-up" x (idx 5)) (p "dev-pass" y (idx 3))
          (p "dev-up" "lk" x lk) (p "dev-pass" "lk" y lk)
          (prec x (idx 2) y (idx 1)))
        (prec x (idx 4) y (idx 1)))))
  (defrule dev-up-completes
    (forall ((x strd))
      (implies (p "dev-up" x (idx 2)) (p "dev-up" x (idx 5)))))
  (defrule dev-open-completes
    (forall ((x strd))
      (implies (p "dev-open" x (idx 2)) (p "dev-open" x (idx 4)))))
  (defrule dev-close-completes
    (forall ((x strd))
      (implies (p "dev-close" x (idx 2)) (p "dev-close" x (idx 4)))))
  (defrule dev-pass-completes
    (forall ((x strd))
      (implies (p "dev-pass" x (idx 2)) (p "dev-pass" x (idx 3)))))
  (defrule dev-up-atomic1
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-up" z (idx 5)) (prec x i1 z (idx 4)))
        (or (= x z) (prec x i1 z (idx 1))))))
  (defrule dev-up-atomic2
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-up" z (idx 5)) (prec z (idx 1) x i1))
        (or (= x z) (prec z (idx 4) x i1)))))
  (defrule dev-open-atomic1
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-open" z (idx 4)) (prec x i1 z (idx 3)))
        (or (= x z) (prec x i1 z (idx 1))))))
  (defrule dev-open-atomic2
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-open" z (idx 4)) (prec z (idx 1) x i1))
        (or (= x z) (prec z (idx 3) x i1)))))
  (defrule dev-close-atomic1
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-close" z (idx 4)) (prec x i1 z (idx 3)))
        (or (= x z) (prec x i1 z (idx 1))))))
  (defrule dev-close-atomic2
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-close" z (idx 4)) (prec z (idx 1) x i1))
        (or (= x z) (prec z (idx 3) x i1)))))
  (defrule dev-pass-atomic1
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-pass" z (idx 3)) (prec x i1 z (idx 2)))
        (or (= x z) (prec x i1 z (idx 1))))))
  (defrule dev-pass-atomic2
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-pass" z (idx 3)) (prec z (idx 1) x i1))
        (or (= x z) (prec z (idx 2) x i1)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule trRl_dev-up-at-4
    (forall ((z strd))
      (implies (p "dev-up" z (idx 5)) (trans z (idx 4)))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd))
      (implies (p "dev-up" z (idx 5)) (trans z (idx 3)))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd))
      (implies (p "dev-up" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd))
      (implies (p "dev-up" z (idx 3)) (trans z (idx 1)))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-open-at-2
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 2)))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd))
      (implies (p "dev-close" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd))
      (implies (p "dev-close" z (idx 4)) (trans z (idx 2)))))
  (defgenrule cau-dev-open-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-open" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-close-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-close" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-pass-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-pass" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1)))))))

(defskeleton atomic-open-closed
  (vars (k skey) (n text) (d o name) (pt pt-0 pval) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (uniq-orig n)
  (traces
    ((recv (enc "may I pass" k)) (load lk (cat pt "st-k" d o k))
      (load ls (cat pt-0 "st" d o o)) (send (enc "you may pass" n k))))
  (label 3)
  (realized)
  (origs (n (0 3)))
  (comment "Not closed under rules"))

(defskeleton atomic-open-closed
  (vars (k skey) (n text) (d o name) (pt pt-0 pval) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (uniq-orig n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (facts (same-dev ls lk))
  (rule gen-state-pass intro-same-dev-pass)
  (traces
    ((recv (enc "may I pass" k)) (load lk (cat pt "st-k" d o k))
      (load ls (cat pt-0 "st" d o o)) (send (enc "you may pass" n k))))
  (label 4)
  (parent 3)
  (unrealized (0 1) (0 2))
  (origs (n (0 3)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 mesg) (k skey) (n text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (start-ch chan) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (precedes ((1 4) (0 1)))
  (uniq-orig n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((1 2) (0 1)))
  (rule atomic-up-pass dev-up-completes intro-same-dev-pass
    intro-same-dev-up same-dev-lk-ls trRl_dev-up-at-1 trRl_dev-up-at-2
    trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation channel-test (added-strand dev-up 3)
    (ch-msg lk (cat pt-1 "st-k" d o k)) (0 1))
  (traces
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k)) (load ls (cat pt-2 old1))
      (stor ls (cat pt-3 "st" d o))))
  (label 5)
  (parent 4)
  (unrealized (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 mesg) (k skey) (n text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (start-ch chan) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand owner-power-dev 1 (k k) (d d) (o o) (start-ch start-ch))
  (precedes ((1 4) (0 1)) ((2 0) (1 0)))
  (uniq-orig n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((1 2) (0 1)))
  (rule intro-same-dev-pass trRl_dev-up-at-1 trRl_dev-up-at-2
    trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation channel-test (added-strand owner-power-dev 1)
    (ch-msg start-ch (cat "power-up" d o k)) (1 0))
  (traces
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k)) (load ls (cat pt-2 old1))
      (stor ls (cat pt-3 "st" d o)))
    ((send start-ch (cat "power-up" d o k))))
  (label 6)
  (parent 5)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 any mesg) (k k-0 skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval) (start-ch chan)
    (ls lk locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand owner-power-dev 1 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (precedes ((1 4) (3 1)) ((2 0) (1 0)) ((3 3) (0 1)))
  (uniq-orig n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k) (cat "st-k" d o k-0))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((1 2) (0 1)) ((3 3) (0 2)))
  (rule cau-dev-pass-2 dev-open-atomic1 gen-state-open
    intro-same-dev-open intro-same-dev-pass invShearsRule same-dev-ls-lk
    trRl_dev-open-at-2 trRl_dev-open-at-3 trRl_dev-up-at-1
    trRl_dev-up-at-2 trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation channel-test (added-strand dev-open 4)
    (ch-msg ls (cat pt "st" d o o)) (0 2))
  (traces
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k)) (load ls (cat pt-2 old1))
      (stor ls (cat pt-3 "st" d o)))
    ((send start-ch (cat "power-up" d o k)))
    ((recv (enc "open" d o n-0 k-0)) (load lk (cat pt-4 "st-k" d o k-0))
      (load ls (cat pt-5 "st" d any)) (stor ls (cat pt "st" d o o))))
  (label 7)
  (parent 6)
  (seen 8)
  (unrealized (3 1))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand owner-power-dev 1 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (precedes ((1 4) (3 1)) ((2 0) (1 0)) ((3 3) (0 1)))
  (uniq-orig n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((1 2) (0 1)) ((1 2) (3 1)) ((3 3) (0 2)))
  (rule intro-same-dev-pass trRl_dev-open-at-2 trRl_dev-open-at-3
    trRl_dev-up-at-1 trRl_dev-up-at-2 trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation channel-test (displaced 4 1 dev-up 3)
    (ch-msg lk (cat pt-5 "st-k" d o k-0)) (3 1))
  (traces
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k)) (load ls (cat pt-2 old1))
      (stor ls (cat pt-3 "st" d o)))
    ((send start-ch (cat "power-up" d o k)))
    ((recv (enc "open" d o n-0 k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt-4 "st" d any)) (stor ls (cat pt "st" d o o))))
  (label 8)
  (parent 7)
  (realized)
  (shape)
  (maps ((0) ((k k) (n n) (d d) (o o) (lk lk) (ls ls))))
  (origs (pt-1 (1 2)) (pt (3 3)) (pt-3 (1 4)) (n (0 3))))

(comment "Nothing left to do")

(defprotocol atomic-open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (stor lk (cat "st-k" d o k)) (load ls old1)
      (stor ls (cat "st" d o)) (send (enc "up" k)))
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
    (trace (recv (enc "open" d o n k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o o)) (send n)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (recv (enc "close" d o n k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o)) (send n)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (recv (enc "may I pass" k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d o o)) (send (enc "you may pass" n k)))
    (uniq-orig n))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z (idx 1)) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z (cat o o)))
        (gen-st (cat "st" d o o)))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d o o)))))
  (defrule gen-state-open
    (forall ((z strd) (d o k mesg))
      (implies
        (and (p "dev-open" "d" z d) (p "dev-open" "o" z o)
          (p "dev-open" "k" z k))
        (gen-st (cat "st-k" d o k)))))
  (defrule gen-state-close
    (forall ((z strd) (d o k mesg))
      (implies
        (and (p "dev-close" "d" z d) (p "dev-close" "o" z o)
          (p "dev-close" "k" z k))
        (gen-st (cat "st-k" d o k)))))
  (defrule gen-state-pass
    (forall ((z strd) (d o k mesg))
      (implies
        (and (p "dev-pass" "d" z d) (p "dev-pass" "o" z o)
          (p "dev-pass" "k" z k))
        (gen-st (cat "st-k" d o k)))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 (idx 2)) (p "dev-up" z2 (idx 2))
          (p "dev-up" "k" z1 k) (p "dev-up" "k" z2 k))
        (= z1 z2))))
  (defrule intro-same-dev-up
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-up" "lk" z lk) (p "dev-up" "ls" z ls))
        (fact same-dev ls lk))))
  (defrule intro-same-dev-open
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-open" "lk" z lk) (p "dev-open" "ls" z ls))
        (fact same-dev ls lk))))
  (defrule intro-same-dev-close
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-close" "lk" z lk) (p "dev-close" "ls" z ls))
        (fact same-dev ls lk))))
  (defrule intro-same-dev-pass
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-pass" "lk" z lk) (p "dev-pass" "ls" z ls))
        (fact same-dev ls lk))))
  (defrule same-dev-ls-lk
    (forall ((ls lk lk-0 locn))
      (implies
        (and (fact same-dev ls lk) (fact same-dev ls lk-0))
        (= lk lk-0))))
  (defrule same-dev-lk-ls
    (forall ((lk ls ls-0 locn))
      (implies
        (and (fact same-dev ls lk) (fact same-dev ls-0 lk))
        (= ls ls-0))))
  (defrule single-thread-up-up
    (forall ((x y strd) (lk locn))
      (implies
        (and (p "dev-up" x (idx 5)) (p "dev-up" y (idx 5))
          (p "dev-up" "lk" x lk) (p "dev-up" "lk" y lk))
        (or
          (= x y)
          (prec x (idx 4) y (idx 1))
          (prec y (idx 4) x (idx 1))))))
  (defrule single-thread-up-open
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-up" x (idx 5)) (p "dev-open" y (idx 4))
          (p "dev-up" "ls" x ls) (p "dev-open" "ls" y ls))
        (or (prec x (idx 4) y (idx 1)) (prec y (idx 3) x (idx 1))))))
  (defrule single-thread-up-close
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-up" x (idx 5)) (p "dev-close" y (idx 4))
          (p "dev-up" "ls" x ls) (p "dev-close" "ls" y ls))
        (or (prec x (idx 4) y (idx 1)) (prec y (idx 3) x (idx 1))))))
  (defrule single-thread-open-open
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-open" x (idx 4)) (p "dev-open" y (idx 4))
          (p "dev-open" "ls" x ls) (p "dev-open" "ls" y ls))
        (or
          (= x y)
          (prec x (idx 3) y (idx 1))
          (prec y (idx 3) x (idx 1))))))
  (defrule single-thread-ls-open-close
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-open" x (idx 4)) (p "dev-close" y (idx 4))
          (p "dev-open" "ls" x ls) (p "dev-close" "ls" y ls))
        (or (prec x (idx 3) y (idx 1)) (prec y (idx 3) x (idx 1))))))
  (defrule single-thread-close-close
    (forall ((x y strd) (ls locn))
      (implies
        (and (p "dev-close" x (idx 4)) (p "dev-close" y (idx 4))
          (p "dev-close" "ls" x ls) (p "dev-close" "ls" y ls))
        (or
          (= x y)
          (prec x (idx 3) y (idx 1))
          (prec y (idx 3) x (idx 1))))))
  (defrule atomic-up-pass
    (forall ((x y strd) (lk locn))
      (implies
        (and (p "dev-up" x (idx 5)) (p "dev-pass" y (idx 3))
          (p "dev-up" "lk" x lk) (p "dev-pass" "lk" y lk)
          (prec x (idx 2) y (idx 1)))
        (prec x (idx 4) y (idx 1)))))
  (defrule dev-up-completes
    (forall ((x strd))
      (implies (p "dev-up" x (idx 2)) (p "dev-up" x (idx 5)))))
  (defrule dev-open-completes
    (forall ((x strd))
      (implies (p "dev-open" x (idx 2)) (p "dev-open" x (idx 4)))))
  (defrule dev-close-completes
    (forall ((x strd))
      (implies (p "dev-close" x (idx 2)) (p "dev-close" x (idx 4)))))
  (defrule dev-pass-completes
    (forall ((x strd))
      (implies (p "dev-pass" x (idx 2)) (p "dev-pass" x (idx 3)))))
  (defrule dev-up-atomic1
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-up" z (idx 5)) (prec x i1 z (idx 4)))
        (or (= x z) (prec x i1 z (idx 1))))))
  (defrule dev-up-atomic2
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-up" z (idx 5)) (prec z (idx 1) x i1))
        (or (= x z) (prec z (idx 4) x i1)))))
  (defrule dev-open-atomic1
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-open" z (idx 4)) (prec x i1 z (idx 3)))
        (or (= x z) (prec x i1 z (idx 1))))))
  (defrule dev-open-atomic2
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-open" z (idx 4)) (prec z (idx 1) x i1))
        (or (= x z) (prec z (idx 3) x i1)))))
  (defrule dev-close-atomic1
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-close" z (idx 4)) (prec x i1 z (idx 3)))
        (or (= x z) (prec x i1 z (idx 1))))))
  (defrule dev-close-atomic2
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-close" z (idx 4)) (prec z (idx 1) x i1))
        (or (= x z) (prec z (idx 3) x i1)))))
  (defrule dev-pass-atomic1
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-pass" z (idx 3)) (prec x i1 z (idx 2)))
        (or (= x z) (prec x i1 z (idx 1))))))
  (defrule dev-pass-atomic2
    (forall ((x z strd) (i1 indx))
      (implies
        (and (p "dev-pass" z (idx 3)) (prec z (idx 1) x i1))
        (or (= x z) (prec z (idx 2) x i1)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule trRl_dev-up-at-4
    (forall ((z strd))
      (implies (p "dev-up" z (idx 5)) (trans z (idx 4)))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd))
      (implies (p "dev-up" z (idx 5)) (trans z (idx 3)))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd))
      (implies (p "dev-up" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd))
      (implies (p "dev-up" z (idx 3)) (trans z (idx 1)))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-open-at-2
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 2)))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd))
      (implies (p "dev-close" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd))
      (implies (p "dev-close" z (idx 4)) (trans z (idx 2)))))
  (defgenrule cau-dev-open-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-open" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-close-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-close" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-pass-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-pass" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1)))))))

(defskeleton atomic-open-closed
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (uniq-orig k n)
  (conf start-ch)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt "st-k" d-0 o-0 k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0))
      (send (enc "you may pass" n k))))
  (label 9)
  (unrealized (0 1) (1 0) (1 1))
  (preskeleton)
  (origs (n (1 3)) (k (0 0)))
  (comment "Not a skeleton"))

(defskeleton atomic-open-closed
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (precedes ((0 0) (1 1)))
  (uniq-orig k n)
  (conf start-ch)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt "st-k" d-0 o-0 k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0))
      (send (enc "you may pass" n k))))
  (label 10)
  (parent 9)
  (unrealized (0 1) (1 0) (1 1))
  (origs (n (1 3)) (k (0 0)))
  (comment "Not closed under rules"))

(defskeleton atomic-open-closed
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (precedes ((0 0) (1 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d-0 o-0 o-0) (cat "st-k" d-0 o-0 k))
  (conf start-ch)
  (facts (same-dev ls lk))
  (rule gen-state-pass intro-same-dev-pass)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt "st-k" d-0 o-0 k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0))
      (send (enc "you may pass" n k))))
  (label 11)
  (parent 10)
  (unrealized (0 1) (1 0) (1 1) (1 2))
  (origs (n (1 3)) (k (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton atomic-open-closed
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (defstrand user-pass 1 (k k))
  (precedes ((0 0) (1 1)) ((2 0) (1 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d-0 o-0 o-0) (cat "st-k" d-0 o-0 k))
  (conf start-ch)
  (facts (same-dev ls lk))
  (rule intro-same-dev-pass)
  (operation encryption-test (added-strand user-pass 1)
    (enc "may I pass" k) (1 0))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt "st-k" d-0 o-0 k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0))
      (send (enc "you may pass" n k))) ((send (enc "may I pass" k))))
  (label 12)
  (parent 11)
  (unrealized (0 1) (1 1) (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton atomic-open-closed
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 1) (1 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d-0 o-0 o-0) (cat "st-k" d-0 o-0 k))
  (conf start-ch)
  (facts (same-dev ls lk))
  (rule intro-same-dev-pass)
  (operation encryption-test (added-listener k) (enc "may I pass" k)
    (1 0))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt "st-k" d-0 o-0 k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0))
      (send (enc "you may pass" n k))) ((recv k) (send k)))
  (label 13)
  (parent 11)
  (seen 15)
  (unrealized (0 1) (1 1) (1 2) (2 0))
  (comment "6 in cohort - 1 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 mesg) (k skey) (n text) (d o d-0 o-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (start-ch start-ch-0 chan)
    (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d-0) (o o-0)
    (start-ch start-ch-0) (lk lk) (ls ls))
  (precedes ((0 0) (3 0)) ((2 0) (1 0)) ((3 4) (1 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d-0 o-0 o-0) (cat "st-k" d-0 o-0 k))
  (conf start-ch)
  (auth start-ch-0)
  (facts (same-dev ls lk))
  (leads-to ((3 2) (1 1)))
  (rule atomic-up-pass dev-up-completes intro-same-dev-pass
    intro-same-dev-up same-dev-lk-ls trRl_dev-up-at-1 trRl_dev-up-at-2
    trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation channel-test (added-strand dev-up 3)
    (ch-msg lk (cat pt-1 "st-k" d-0 o-0 k)) (1 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d-0 o-0 k))
      (load ls (cat pt "st" d-0 o-0 o-0))
      (send (enc "you may pass" n k))) ((send (enc "may I pass" k)))
    ((recv start-ch-0 (cat "power-up" d-0 o-0 k))
      (load lk (cat pt-0 old)) (stor lk (cat pt-1 "st-k" d-0 o-0 k))
      (load ls (cat pt-2 old1)) (stor ls (cat pt-3 "st" d-0 o-0))))
  (label 14)
  (parent 12)
  (unrealized (0 1) (1 2) (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 mesg) (k skey) (n text) (d o d-0 o-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan)
    (lk ls lk-0 ls-0 locn))
  (defstrand owner-power-dev 2 (k k) (d d-0) (o o-0)
    (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (deflistener k)
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d-0) (o o-0)
    (start-ch start-ch) (lk lk-0) (ls ls-0))
  (precedes ((0 0) (3 0)) ((2 1) (1 0)) ((3 4) (2 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls-0 lk-0) (same-dev ls lk))
  (rule dev-up-atomic2 dev-up-completes intro-same-dev-pass
    intro-same-dev-up trRl_dev-up-at-1 trRl_dev-up-at-2 trRl_dev-up-at-3
    trRl_dev-up-at-4)
  (operation nonce-test (added-strand dev-up 3) k (2 0)
    (ch-msg start-ch (cat "power-up" d-0 o-0 k)))
  (traces
    ((send start-ch (cat "power-up" d-0 o-0 k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt "st-k" d o k))
      (load ls (cat pt-0 "st" d o o)) (send (enc "you may pass" n k)))
    ((recv k) (send k))
    ((recv start-ch (cat "power-up" d-0 o-0 k))
      (load lk-0 (cat pt-1 old)) (stor lk-0 (cat pt-2 "st-k" d-0 o-0 k))
      (load ls-0 (cat pt-3 old1)) (stor ls-0 (cat pt-4 "st" d-0 o-0))))
  (label 15)
  (parent 13)
  (seen 15)
  (unrealized (0 1) (1 1) (1 2) (2 0))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 mesg) (k skey) (n text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (precedes ((0 0) (3 0)) ((2 0) (1 0)) ((3 4) (1 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((3 2) (1 1)))
  (rule intro-same-dev-pass trRl_dev-up-at-1 trRl_dev-up-at-2
    trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation channel-test (displaced 4 0 owner-power-dev 1)
    (ch-msg start-ch-0 (cat "power-up" d-0 o-0 k)) (3 0))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((send (enc "may I pass" k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k)) (load ls (cat pt-2 old1))
      (stor ls (cat pt-3 "st" d o))))
  (label 16)
  (parent 14)
  (unrealized (0 1) (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 any mesg) (k k-0 skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval) (start-ch chan)
    (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (precedes ((0 0) (3 0)) ((2 0) (1 0)) ((3 4) (4 1)) ((4 3) (1 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k) (cat "st-k" d o k-0))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((3 2) (1 1)) ((4 3) (1 2)))
  (rule cau-dev-pass-2 dev-open-atomic1 gen-state-open
    intro-same-dev-open intro-same-dev-pass invShearsRule same-dev-ls-lk
    trRl_dev-open-at-2 trRl_dev-open-at-3 trRl_dev-up-at-1
    trRl_dev-up-at-2 trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation channel-test (added-strand dev-open 4)
    (ch-msg ls (cat pt "st" d o o)) (1 2))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((send (enc "may I pass" k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k)) (load ls (cat pt-2 old1))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k-0)) (load lk (cat pt-4 "st-k" d o k-0))
      (load ls (cat pt-5 "st" d any)) (stor ls (cat pt "st" d o o))))
  (label 17)
  (parent 16)
  (seen 18)
  (unrealized (0 1) (4 1))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (precedes ((0 0) (3 0)) ((2 0) (1 0)) ((3 4) (4 1)) ((4 3) (1 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((3 2) (1 1)) ((3 2) (4 1)) ((4 3) (1 2)))
  (rule intro-same-dev-pass trRl_dev-open-at-2 trRl_dev-open-at-3
    trRl_dev-up-at-1 trRl_dev-up-at-2 trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation channel-test (displaced 5 3 dev-up 3)
    (ch-msg lk (cat pt-5 "st-k" d o k-0)) (4 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((send (enc "may I pass" k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k)) (load ls (cat pt-2 old1))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt-4 "st" d any)) (stor ls (cat pt "st" d o o))))
  (label 18)
  (parent 17)
  (unrealized (0 1) (4 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand owner-open 1 (k k) (n n-0) (d d) (o o))
  (precedes ((0 0) (3 0)) ((2 0) (1 0)) ((3 4) (4 1)) ((4 3) (1 1))
    ((5 0) (4 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((3 2) (1 1)) ((3 2) (4 1)) ((4 3) (1 2)))
  (rule intro-same-dev-pass trRl_dev-open-at-2 trRl_dev-open-at-3
    trRl_dev-up-at-1 trRl_dev-up-at-2 trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation encryption-test (added-strand owner-open 1)
    (enc "open" d o n-0 k) (4 0))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((send (enc "may I pass" k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k)) (load ls (cat pt-2 old1))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt-4 "st" d any)) (stor ls (cat pt "st" d o o)))
    ((send (enc "open" d o n-0 k))))
  (label 19)
  (parent 18)
  (seen 21)
  (unrealized (0 1))
  (comment "3 in cohort - 2 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (deflistener k)
  (precedes ((0 0) (3 0)) ((0 0) (5 0)) ((2 0) (1 0)) ((3 4) (4 1))
    ((4 3) (1 1)) ((5 1) (4 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((3 2) (1 1)) ((3 2) (4 1)) ((4 3) (1 2)))
  (rule intro-same-dev-pass trRl_dev-open-at-2 trRl_dev-open-at-3
    trRl_dev-up-at-1 trRl_dev-up-at-2 trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation encryption-test (added-listener k) (enc "open" d o n-0 k)
    (4 0))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((send (enc "may I pass" k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k)) (load ls (cat pt-2 old1))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt-4 "st" d any)) (stor ls (cat pt "st" d o o)))
    ((recv k) (send k)))
  (label 20)
  (parent 18)
  (seen 23)
  (unrealized (0 1) (5 0))
  (comment "4 in cohort - 1 not yet seen"))

(defskeleton atomic-open-closed
  (vars (any old old1 mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand owner-open 1 (k k) (n n-0) (d d) (o o))
  (defstrand dev-up 6 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (precedes ((0 0) (5 0)) ((2 0) (1 0)) ((3 3) (1 1)) ((4 0) (3 0))
    ((5 4) (3 1)) ((5 5) (0 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((3 3) (1 2)) ((5 2) (1 1)) ((5 2) (3 1)))
  (rule intro-same-dev-pass trRl_dev-open-at-2 trRl_dev-open-at-3
    trRl_dev-up-at-1 trRl_dev-up-at-2 trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation encryption-test (displaced 3 6 dev-up 6) (enc "up" k)
    (0 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt-2 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((send (enc "may I pass" k)))
    ((recv (enc "open" d o n-0 k)) (load lk (cat pt-2 "st-k" d o k))
      (load ls (cat pt-0 "st" d any)) (stor ls (cat pt "st" d o o)))
    ((send (enc "open" d o n-0 k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-1 old))
      (stor lk (cat pt-2 "st-k" d o k)) (load ls (cat pt-3 old1))
      (stor ls (cat pt-4 "st" d o)) (send (enc "up" k))))
  (label 21)
  (parent 19)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((k k) (d d) (o o) (start-ch start-ch) (n n) (d-0 d) (o-0 o)
        (lk lk) (ls ls))))
  (origs (pt-2 (5 2)) (pt-4 (5 4)) (pt (3 3)) (n (1 3)) (k (0 0))))

(defskeleton atomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand owner-open 1 (k k) (n n-0) (d d) (o o))
  (deflistener k)
  (precedes ((0 0) (3 0)) ((0 0) (6 0)) ((2 0) (1 0)) ((3 4) (4 1))
    ((4 3) (1 1)) ((5 0) (4 0)) ((6 1) (0 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((3 2) (1 1)) ((3 2) (4 1)) ((4 3) (1 2)))
  (rule intro-same-dev-pass trRl_dev-open-at-2 trRl_dev-open-at-3
    trRl_dev-up-at-1 trRl_dev-up-at-2 trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation encryption-test (added-listener k) (enc "up" k) (0 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((send (enc "may I pass" k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k)) (load ls (cat pt-2 old1))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt-4 "st" d any)) (stor ls (cat pt "st" d o o)))
    ((send (enc "open" d o n-0 k))) ((recv k) (send k)))
  (label 22)
  (parent 19)
  (seen 24)
  (unrealized (6 0))
  (comment "4 in cohort - 1 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (deflistener k)
  (precedes ((0 0) (3 0)) ((2 0) (1 0)) ((3 4) (5 0)) ((4 3) (1 1))
    ((5 1) (4 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((3 2) (1 1)) ((3 2) (4 1)) ((4 3) (1 2)))
  (rule dev-up-atomic2 intro-same-dev-pass trRl_dev-open-at-2
    trRl_dev-open-at-3 trRl_dev-up-at-1 trRl_dev-up-at-2
    trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation nonce-test (displaced 6 3 dev-up 3) k (5 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((send (enc "may I pass" k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k)) (load ls (cat pt-2 old1))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt-4 "st" d any)) (stor ls (cat pt "st" d o o)))
    ((recv k) (send k)))
  (label 23)
  (parent 20)
  (seen 23)
  (unrealized (0 1) (5 0))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton atomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand owner-open 1 (k k) (n n-0) (d d) (o o))
  (deflistener k)
  (precedes ((0 0) (3 0)) ((2 0) (1 0)) ((3 4) (4 1)) ((3 4) (6 0))
    ((4 3) (1 1)) ((5 0) (4 0)) ((6 1) (0 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk))
  (leads-to ((3 2) (1 1)) ((3 2) (4 1)) ((4 3) (1 2)))
  (rule dev-up-atomic2 intro-same-dev-pass trRl_dev-open-at-2
    trRl_dev-open-at-3 trRl_dev-up-at-1 trRl_dev-up-at-2
    trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation nonce-test (displaced 7 3 dev-up 3) k (6 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv (enc "may I pass" k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((send (enc "may I pass" k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k)) (load ls (cat pt-2 old1))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load lk (cat pt-1 "st-k" d o k))
      (load ls (cat pt-4 "st" d any)) (stor ls (cat pt "st" d o o)))
    ((send (enc "open" d o n-0 k))) ((recv k) (send k)))
  (label 24)
  (parent 22)
  (seen 24)
  (unrealized (6 0))
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")
