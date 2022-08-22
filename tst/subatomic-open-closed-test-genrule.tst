(herald subatomic-open-closed-test-genrule (bound 40))

(comment "CPSA 4.3.1")
(comment
  "All input read from tst/subatomic-open-closed-test-genrule.scm")
(comment "Strand count bounded at 40")

(defprotocol subatomic-open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (load ls old1) (stor lk (cat "st-k" d o k))
      (stor ls (cat "st" d o)) (send (enc "up" k)))
    (auth start-ch)
    (critical-sections (1 4))
    (facts (same-dev ls lk)))
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
    (trace (recv (enc "open" d o n k)) (load ls (cat "st" d any))
      (load lk (cat "st-k" d o k)) (stor ls (cat "st" d o o)) (send n))
    (critical-sections (1 3))
    (gen-st (cat "st-k" d o k) (cat "st" d (cat o o)))
    (facts (same-dev ls lk)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (recv (enc "close" d o n k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o)) (send n))
    (gen-st (cat "st-k" d o k))
    (critical-sections (1 3))
    (facts (same-dev ls lk)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (load ls (cat "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    (uniq-orig n)
    (gen-st (cat "st-k" d o k) (cat "st" d (cat o o)))
    (critical-sections (0 1))
    (facts (same-dev ls lk)))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 2) (p "dev-up" z2 2) (p "dev-up" "k" z1 k)
          (p "dev-up" "k" z2 k))
        (= z1 z2))))
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
  (defgenrule fact-dev-up-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-up" z 3) (p "dev-up" "lk" z lk)
          (p "dev-up" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-open-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-open" z 3) (p "dev-open" "lk" z lk)
          (p "dev-open" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-close-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-close" z 3) (p "dev-close" "lk" z lk)
          (p "dev-close" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-pass-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-pass" z 2) (p "dev-pass" "lk" z lk)
          (p "dev-pass" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-up-at-4
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 4))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd)) (implies (p "dev-up" z 4) (trans z 3))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 2))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd)) (implies (p "dev-up" z 4) (trans z 1))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 3))))
  (defgenrule trRl_dev-open-at-1
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 1))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 3))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 2))))
  (defgenrule eff-dev-up-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 4) (prec z 3 z1 i))
        (or (= z z1) (and (p "dev-up" z 5) (prec z 4 z1 i))))))
  (defgenrule cau-dev-up-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-open-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-open" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-close-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-close" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-pass-1
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-pass" z 2) (prec z1 i z 1))
        (or (= z z1) (prec z1 i z 0)))))
  (defgenrule gen-st-dev-open-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "o" z o)
          (p "dev-open" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule gen-st-dev-close-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-close" z 1) (p "dev-close" "k" z k)
          (p "dev-close" "o" z o) (p "dev-close" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "o" z o)
          (p "dev-pass" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "o" z o)
          (p "dev-pass" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule fact-dev-pass-same-dev0
    (forall ((z strd) (ls lk locn))
      (implies
        (and (p "dev-pass" z 2) (p "dev-pass" "ls" z ls)
          (p "dev-pass" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd)) (implies (p "dev-close" z 3) (trans z 2))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 3))))
  (defgenrule gen-st-dev-close-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-close" z 1) (p "dev-close" "k" z k)
          (p "dev-close" "o" z o) (p "dev-close" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule fact-dev-close-same-dev0
    (forall ((z strd) (ls lk locn))
      (implies
        (and (p "dev-close" z 3) (p "dev-close" "ls" z ls)
          (p "dev-close" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-open-at-1
    (forall ((z strd)) (implies (p "dev-open" z 2) (trans z 1))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 3))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "o" z o)
          (p "dev-open" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule gen-st-dev-open-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule fact-dev-open-same-dev0
    (forall ((z strd) (ls lk locn))
      (implies
        (and (p "dev-open" z 3) (p "dev-open" "ls" z ls)
          (p "dev-open" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd)) (implies (p "dev-up" z 2) (trans z 1))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd)) (implies (p "dev-up" z 3) (trans z 2))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd)) (implies (p "dev-up" z 4) (trans z 3))))
  (defgenrule trRl_dev-up-at-4
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 4))))
  (defgenrule fact-dev-up-same-dev0
    (forall ((z strd) (ls lk locn))
      (implies
        (and (p "dev-up" z 3) (p "dev-up" "ls" z ls)
          (p "dev-up" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cau-dev-pass-1
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-pass" z 2) (prec z1 i z 1))
        (or (= z z1) (prec z1 i z 0)))))
  (defgenrule cau-dev-close-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-close" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-open-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-open" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-up-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule eff-dev-up-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 4) (prec z 3 z1 i))
        (or (= z z1) (and (p "dev-up" z 5) (prec z 4 z1 i))))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

(defskeleton subatomic-open-closed
  (vars (k skey) (d o name) (start-ch chan))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (deflistener k)
  (uniq-orig k)
  (conf start-ch)
  (facts (no-state-split))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv k) (send k)))
  (label 0)
  (unrealized (0 1) (1 0))
  (preskeleton)
  (origs (k (0 0)))
  (comment "Not a skeleton"))

(defskeleton subatomic-open-closed
  (vars (k skey) (d o name) (start-ch chan))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (deflistener k)
  (precedes ((0 0) (1 0)))
  (uniq-orig k)
  (conf start-ch)
  (facts (no-state-split))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv k) (send k)))
  (label 1)
  (parent 0)
  (seen 2)
  (unrealized (0 1) (1 0))
  (origs (k (0 0)))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton subatomic-open-closed
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
  (facts (trans 2 4) (trans 2 2) (same-dev ls lk) (trans 2 3)
    (trans 2 1) (no-state-split))
  (rule trRl_dev-up-at-4 trRl_dev-up-at-2 eff-dev-up-3
    fact-dev-up-same-dev0 trRl_dev-up-at-3 trRl_dev-up-at-1)
  (operation nonce-test (added-strand dev-up 4) k (1 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv k) (send k))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt old))
      (load ls (cat pt-0 old1)) (stor lk (cat pt-1 "st-k" d o k))
      (stor ls (cat pt-2 "st" d o))))
  (label 2)
  (parent 1)
  (seen 2)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol subatomic-open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (load ls old1) (stor lk (cat "st-k" d o k))
      (stor ls (cat "st" d o)) (send (enc "up" k)))
    (auth start-ch)
    (critical-sections (1 4))
    (facts (same-dev ls lk)))
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
    (trace (recv (enc "open" d o n k)) (load ls (cat "st" d any))
      (load lk (cat "st-k" d o k)) (stor ls (cat "st" d o o)) (send n))
    (critical-sections (1 3))
    (gen-st (cat "st-k" d o k) (cat "st" d (cat o o)))
    (facts (same-dev ls lk)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (recv (enc "close" d o n k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o)) (send n))
    (gen-st (cat "st-k" d o k))
    (critical-sections (1 3))
    (facts (same-dev ls lk)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (load ls (cat "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    (uniq-orig n)
    (gen-st (cat "st-k" d o k) (cat "st" d (cat o o)))
    (critical-sections (0 1))
    (facts (same-dev ls lk)))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 2) (p "dev-up" z2 2) (p "dev-up" "k" z1 k)
          (p "dev-up" "k" z2 k))
        (= z1 z2))))
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
  (defgenrule fact-dev-up-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-up" z 3) (p "dev-up" "lk" z lk)
          (p "dev-up" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-open-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-open" z 3) (p "dev-open" "lk" z lk)
          (p "dev-open" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-close-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-close" z 3) (p "dev-close" "lk" z lk)
          (p "dev-close" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-pass-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-pass" z 2) (p "dev-pass" "lk" z lk)
          (p "dev-pass" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-up-at-4
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 4))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd)) (implies (p "dev-up" z 4) (trans z 3))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 2))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd)) (implies (p "dev-up" z 4) (trans z 1))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 3))))
  (defgenrule trRl_dev-open-at-1
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 1))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 3))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 2))))
  (defgenrule eff-dev-up-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 4) (prec z 3 z1 i))
        (or (= z z1) (and (p "dev-up" z 5) (prec z 4 z1 i))))))
  (defgenrule cau-dev-up-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-open-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-open" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-close-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-close" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-pass-1
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-pass" z 2) (prec z1 i z 1))
        (or (= z z1) (prec z1 i z 0)))))
  (defgenrule gen-st-dev-open-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "o" z o)
          (p "dev-open" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule gen-st-dev-close-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-close" z 1) (p "dev-close" "k" z k)
          (p "dev-close" "o" z o) (p "dev-close" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "o" z o)
          (p "dev-pass" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "o" z o)
          (p "dev-pass" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule fact-dev-pass-same-dev0
    (forall ((z strd) (ls lk locn))
      (implies
        (and (p "dev-pass" z 2) (p "dev-pass" "ls" z ls)
          (p "dev-pass" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd)) (implies (p "dev-close" z 3) (trans z 2))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 3))))
  (defgenrule gen-st-dev-close-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-close" z 1) (p "dev-close" "k" z k)
          (p "dev-close" "o" z o) (p "dev-close" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule fact-dev-close-same-dev0
    (forall ((z strd) (ls lk locn))
      (implies
        (and (p "dev-close" z 3) (p "dev-close" "ls" z ls)
          (p "dev-close" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-open-at-1
    (forall ((z strd)) (implies (p "dev-open" z 2) (trans z 1))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 3))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "o" z o)
          (p "dev-open" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule gen-st-dev-open-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule fact-dev-open-same-dev0
    (forall ((z strd) (ls lk locn))
      (implies
        (and (p "dev-open" z 3) (p "dev-open" "ls" z ls)
          (p "dev-open" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd)) (implies (p "dev-up" z 2) (trans z 1))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd)) (implies (p "dev-up" z 3) (trans z 2))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd)) (implies (p "dev-up" z 4) (trans z 3))))
  (defgenrule trRl_dev-up-at-4
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 4))))
  (defgenrule fact-dev-up-same-dev0
    (forall ((z strd) (ls lk locn))
      (implies
        (and (p "dev-up" z 3) (p "dev-up" "ls" z ls)
          (p "dev-up" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cau-dev-pass-1
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-pass" z 2) (prec z1 i z 1))
        (or (= z z1) (prec z1 i z 0)))))
  (defgenrule cau-dev-close-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-close" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-open-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-open" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-up-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule eff-dev-up-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 4) (prec z 3 z1 i))
        (or (= z z1) (and (p "dev-up" z 5) (prec z 4 z1 i))))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

(defskeleton subatomic-open-closed
  (vars (k skey) (n text) (d o name) (pt pt-0 pval) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (uniq-orig n)
  (facts (no-state-split))
  (traces
    ((load lk (cat pt "st-k" d o k)) (load ls (cat pt-0 "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k))))
  (label 3)
  (realized)
  (origs (n (0 3)))
  (comment "Not closed under rules"))

(defskeleton subatomic-open-closed
  (vars (k skey) (n text) (d o name) (pt pt-0 pval) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (uniq-orig n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (facts (same-dev ls lk) (no-state-split))
  (rule fact-dev-pass-same-dev0 gen-st-dev-pass-1 gen-st-dev-pass-0)
  (traces
    ((load lk (cat pt "st-k" d o k)) (load ls (cat pt-0 "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k))))
  (label 4)
  (parent 3)
  (seen 5)
  (unrealized (0 0) (0 1))
  (origs (n (0 3)))
  (comment "6 in cohort - 1 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 mesg) (k skey) (n text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (start-ch chan) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (precedes ((1 4) (0 0)))
  (uniq-orig n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (auth start-ch)
  (facts (trans 1 4) (trans 1 2) (same-dev ls lk) (trans 1 3)
    (trans 1 1) (no-state-split))
  (rule cau-dev-pass-1 eff-dev-up-3 trRl_dev-up-at-4 trRl_dev-up-at-2
    same-dev-lk-ls fact-dev-up-same-dev0 trRl_dev-up-at-3
    trRl_dev-up-at-1)
  (operation channel-test (added-strand dev-up 4)
    (ch-msg lk (cat pt-2 "st-k" d o k)) (0 0))
  (traces
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o))))
  (label 5)
  (parent 4)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 mesg) (k skey) (n text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (start-ch chan) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand owner-power-dev 1 (k k) (d d) (o o) (start-ch start-ch))
  (precedes ((1 4) (0 0)) ((2 0) (1 0)))
  (uniq-orig n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (trans 1 4) (trans 1 2) (same-dev ls lk) (trans 1 3)
    (trans 1 1) (no-state-split))
  (operation channel-test (added-strand owner-power-dev 1)
    (ch-msg start-ch (cat "power-up" d o k)) (1 0))
  (traces
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((send start-ch (cat "power-up" d o k))))
  (label 6)
  (parent 5)
  (seen 7)
  (unrealized (0 1))
  (comment "104 in cohort - 1 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k k-0 skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval) (start-ch chan)
    (ls lk locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand owner-power-dev 1 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (precedes ((1 4) (3 1)) ((2 0) (1 0)) ((3 3) (0 0)))
  (uniq-orig n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k) (cat "st-k" d o k-0))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 1 4)
    (trans 1 2) (trans 1 3) (trans 1 1) (no-state-split))
  (rule eff-dev-up-3 cau-dev-open-2 invShearsRule cau-dev-pass-1
    same-dev-ls-lk fact-dev-open-same-dev0 trRl_dev-open-at-3
    trRl_dev-open-at-1 gen-st-dev-open-1)
  (operation channel-test (added-strand dev-open 4)
    (ch-msg ls (cat pt "st" d o o)) (0 1))
  (traces
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((send start-ch (cat "power-up" d o k)))
    ((recv (enc "open" d o n-0 k-0)) (load ls (cat pt-4 "st" d any))
      (load lk (cat pt-5 "st-k" d o k-0))
      (stor ls (cat pt "st" d o o))))
  (label 7)
  (parent 6)
  (seen 8)
  (unrealized (3 2))
  (comment "57 in cohort - 1 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand owner-power-dev 1 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (precedes ((1 4) (3 1)) ((2 0) (1 0)) ((3 3) (0 0)))
  (uniq-orig n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 1 4)
    (trans 1 2) (trans 1 3) (trans 1 1) (no-state-split))
  (operation channel-test (displaced 4 1 dev-up 4)
    (ch-msg lk (cat pt-5 "st-k" d o k-0)) (3 2))
  (traces
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((send start-ch (cat "power-up" d o k)))
    ((recv (enc "open" d o n-0 k)) (load ls (cat pt-4 "st" d any))
      (load lk (cat pt-2 "st-k" d o k)) (stor ls (cat pt "st" d o o))))
  (label 8)
  (parent 7)
  (realized)
  (shape)
  (maps
    ((0) ((k k) (n n) (d d) (o o) (lk lk) (ls ls) (pt pt-2) (pt-0 pt))))
  (origs (pt-2 (1 3)) (pt-3 (1 4)) (pt (3 3)) (n (0 3))))

(comment "Nothing left to do")

(defprotocol subatomic-open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (load ls old1) (stor lk (cat "st-k" d o k))
      (stor ls (cat "st" d o)) (send (enc "up" k)))
    (auth start-ch)
    (critical-sections (1 4))
    (facts (same-dev ls lk)))
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
    (trace (recv (enc "open" d o n k)) (load ls (cat "st" d any))
      (load lk (cat "st-k" d o k)) (stor ls (cat "st" d o o)) (send n))
    (critical-sections (1 3))
    (gen-st (cat "st-k" d o k) (cat "st" d (cat o o)))
    (facts (same-dev ls lk)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (recv (enc "close" d o n k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o)) (send n))
    (gen-st (cat "st-k" d o k))
    (critical-sections (1 3))
    (facts (same-dev ls lk)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (load ls (cat "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    (uniq-orig n)
    (gen-st (cat "st-k" d o k) (cat "st" d (cat o o)))
    (critical-sections (0 1))
    (facts (same-dev ls lk)))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 2) (p "dev-up" z2 2) (p "dev-up" "k" z1 k)
          (p "dev-up" "k" z2 k))
        (= z1 z2))))
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
  (defgenrule fact-dev-up-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-up" z 3) (p "dev-up" "lk" z lk)
          (p "dev-up" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-open-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-open" z 3) (p "dev-open" "lk" z lk)
          (p "dev-open" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-close-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-close" z 3) (p "dev-close" "lk" z lk)
          (p "dev-close" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-pass-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-pass" z 2) (p "dev-pass" "lk" z lk)
          (p "dev-pass" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-up-at-4
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 4))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd)) (implies (p "dev-up" z 4) (trans z 3))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 2))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd)) (implies (p "dev-up" z 4) (trans z 1))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 3))))
  (defgenrule trRl_dev-open-at-1
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 1))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 3))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 2))))
  (defgenrule eff-dev-up-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 4) (prec z 3 z1 i))
        (or (= z z1) (and (p "dev-up" z 5) (prec z 4 z1 i))))))
  (defgenrule cau-dev-up-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-open-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-open" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-close-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-close" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-pass-1
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-pass" z 2) (prec z1 i z 1))
        (or (= z z1) (prec z1 i z 0)))))
  (defgenrule gen-st-dev-open-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "o" z o)
          (p "dev-open" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule gen-st-dev-close-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-close" z 1) (p "dev-close" "k" z k)
          (p "dev-close" "o" z o) (p "dev-close" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "o" z o)
          (p "dev-pass" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "o" z o)
          (p "dev-pass" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule fact-dev-pass-same-dev0
    (forall ((z strd) (ls lk locn))
      (implies
        (and (p "dev-pass" z 2) (p "dev-pass" "ls" z ls)
          (p "dev-pass" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd)) (implies (p "dev-close" z 3) (trans z 2))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 3))))
  (defgenrule gen-st-dev-close-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-close" z 1) (p "dev-close" "k" z k)
          (p "dev-close" "o" z o) (p "dev-close" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule fact-dev-close-same-dev0
    (forall ((z strd) (ls lk locn))
      (implies
        (and (p "dev-close" z 3) (p "dev-close" "ls" z ls)
          (p "dev-close" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-open-at-1
    (forall ((z strd)) (implies (p "dev-open" z 2) (trans z 1))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 3))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "o" z o)
          (p "dev-open" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule gen-st-dev-open-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule fact-dev-open-same-dev0
    (forall ((z strd) (ls lk locn))
      (implies
        (and (p "dev-open" z 3) (p "dev-open" "ls" z ls)
          (p "dev-open" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd)) (implies (p "dev-up" z 2) (trans z 1))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd)) (implies (p "dev-up" z 3) (trans z 2))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd)) (implies (p "dev-up" z 4) (trans z 3))))
  (defgenrule trRl_dev-up-at-4
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 4))))
  (defgenrule fact-dev-up-same-dev0
    (forall ((z strd) (ls lk locn))
      (implies
        (and (p "dev-up" z 3) (p "dev-up" "ls" z ls)
          (p "dev-up" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cau-dev-pass-1
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-pass" z 2) (prec z1 i z 1))
        (or (= z z1) (prec z1 i z 0)))))
  (defgenrule cau-dev-close-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-close" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-open-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-open" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-up-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule eff-dev-up-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 4) (prec z 3 z1 i))
        (or (= z z1) (and (p "dev-up" z 5) (prec z 4 z1 i))))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

(defskeleton subatomic-open-closed
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (uniq-orig k n)
  (conf start-ch)
  (facts (no-state-split))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt "st-k" d-0 o-0 k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0)) (recv (enc "may I pass" k))
      (send (enc "you may pass" n k))))
  (label 9)
  (unrealized (0 1) (1 0) (1 2))
  (preskeleton)
  (origs (n (1 3)) (k (0 0)))
  (comment "Not a skeleton"))

(defskeleton subatomic-open-closed
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (precedes ((0 0) (1 0)))
  (uniq-orig k n)
  (conf start-ch)
  (facts (no-state-split))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt "st-k" d-0 o-0 k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0)) (recv (enc "may I pass" k))
      (send (enc "you may pass" n k))))
  (label 10)
  (parent 9)
  (unrealized (0 1) (1 0) (1 2))
  (origs (n (1 3)) (k (0 0)))
  (comment "Not closed under rules"))

(defskeleton subatomic-open-closed
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (precedes ((0 0) (1 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d-0 o-0 o-0) (cat "st-k" d-0 o-0 k))
  (conf start-ch)
  (facts (same-dev ls lk) (no-state-split))
  (rule fact-dev-pass-same-dev0 gen-st-dev-pass-1 gen-st-dev-pass-0)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt "st-k" d-0 o-0 k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0)) (recv (enc "may I pass" k))
      (send (enc "you may pass" n k))))
  (label 11)
  (parent 10)
  (seen 12)
  (unrealized (0 1) (1 0) (1 1) (1 2))
  (origs (n (1 3)) (k (0 0)))
  (comment "6 in cohort - 1 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 mesg) (k skey) (n text) (d o d-0 o-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (start-ch start-ch-0 chan)
    (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d-0) (o o-0)
    (start-ch start-ch-0) (lk lk) (ls ls))
  (precedes ((0 0) (2 0)) ((2 4) (1 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d-0 o-0 o-0) (cat "st-k" d-0 o-0 k))
  (conf start-ch)
  (auth start-ch-0)
  (facts (trans 2 4) (trans 2 2) (same-dev ls lk) (trans 2 3)
    (trans 2 1) (no-state-split))
  (rule cau-dev-pass-1 eff-dev-up-3 trRl_dev-up-at-4 trRl_dev-up-at-2
    same-dev-lk-ls fact-dev-up-same-dev0 trRl_dev-up-at-3
    trRl_dev-up-at-1)
  (operation channel-test (added-strand dev-up 4)
    (ch-msg lk (cat pt-2 "st-k" d-0 o-0 k)) (1 0))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-2 "st-k" d-0 o-0 k))
      (load ls (cat pt "st" d-0 o-0 o-0)) (recv (enc "may I pass" k))
      (send (enc "you may pass" n k)))
    ((recv start-ch-0 (cat "power-up" d-0 o-0 k))
      (load lk (cat pt-0 old)) (load ls (cat pt-1 old1))
      (stor lk (cat pt-2 "st-k" d-0 o-0 k))
      (stor ls (cat pt-3 "st" d-0 o-0))))
  (label 12)
  (parent 11)
  (unrealized (0 1) (1 1) (1 2) (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 mesg) (k skey) (n text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (precedes ((0 0) (2 0)) ((2 4) (1 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (trans 2 4) (trans 2 2) (same-dev ls lk) (trans 2 3)
    (trans 2 1) (no-state-split))
  (operation channel-test (displaced 3 0 owner-power-dev 1)
    (ch-msg start-ch-0 (cat "power-up" d-0 o-0 k)) (2 0))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o))))
  (label 13)
  (parent 12)
  (seen 14)
  (unrealized (0 1) (1 1) (1 2))
  (comment "104 in cohort - 1 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k k-0 skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval) (start-ch chan)
    (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (precedes ((0 0) (2 0)) ((2 4) (3 1)) ((3 3) (1 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k) (cat "st-k" d o k-0))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 2 4)
    (trans 2 2) (trans 2 3) (trans 2 1) (no-state-split))
  (rule eff-dev-up-3 cau-dev-open-2 invShearsRule cau-dev-pass-1
    same-dev-ls-lk fact-dev-open-same-dev0 trRl_dev-open-at-3
    trRl_dev-open-at-1 gen-st-dev-open-1)
  (operation channel-test (added-strand dev-open 4)
    (ch-msg ls (cat pt "st" d o o)) (1 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k-0)) (load ls (cat pt-4 "st" d any))
      (load lk (cat pt-5 "st-k" d o k-0))
      (stor ls (cat pt "st" d o o))))
  (label 14)
  (parent 13)
  (seen 15)
  (unrealized (0 1) (1 2) (3 2))
  (comment "57 in cohort - 1 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (precedes ((0 0) (2 0)) ((2 4) (3 1)) ((3 3) (1 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 2 4)
    (trans 2 2) (trans 2 3) (trans 2 1) (no-state-split))
  (operation channel-test (displaced 4 2 dev-up 4)
    (ch-msg lk (cat pt-5 "st-k" d o k-0)) (3 2))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load ls (cat pt-4 "st" d any))
      (load lk (cat pt-2 "st-k" d o k)) (stor ls (cat pt "st" d o o))))
  (label 15)
  (parent 14)
  (unrealized (0 1) (1 2) (3 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand owner-open 1 (k k) (n n-0) (d d) (o o))
  (precedes ((0 0) (2 0)) ((2 4) (3 1)) ((3 3) (1 0)) ((4 0) (3 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 2 4)
    (trans 2 2) (trans 2 3) (trans 2 1) (no-state-split))
  (operation encryption-test (added-strand owner-open 1)
    (enc "open" d o n-0 k) (3 0))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load ls (cat pt-4 "st" d any))
      (load lk (cat pt-2 "st-k" d o k)) (stor ls (cat pt "st" d o o)))
    ((send (enc "open" d o n-0 k))))
  (label 16)
  (parent 15)
  (unrealized (0 1) (1 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((0 0) (4 0)) ((2 4) (3 1)) ((3 3) (1 0))
    ((4 1) (3 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 2 4)
    (trans 2 2) (trans 2 3) (trans 2 1) (no-state-split))
  (operation encryption-test (added-listener k) (enc "open" d o n-0 k)
    (3 0))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load ls (cat pt-4 "st" d any))
      (load lk (cat pt-2 "st-k" d o k)) (stor ls (cat pt "st" d o o)))
    ((recv k) (send k)))
  (label 17)
  (parent 15)
  (seen 20)
  (unrealized (0 1) (4 0))
  (comment "8 in cohort - 1 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand owner-open 1 (k k) (n n-0) (d d) (o o))
  (defstrand user-pass 1 (k k))
  (precedes ((0 0) (2 0)) ((2 4) (3 1)) ((3 3) (1 0)) ((4 0) (3 0))
    ((5 0) (1 2)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 2 4)
    (trans 2 2) (trans 2 3) (trans 2 1) (no-state-split))
  (operation encryption-test (added-strand user-pass 1)
    (enc "may I pass" k) (1 2))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load ls (cat pt-4 "st" d any))
      (load lk (cat pt-2 "st-k" d o k)) (stor ls (cat pt "st" d o o)))
    ((send (enc "open" d o n-0 k))) ((send (enc "may I pass" k))))
  (label 18)
  (parent 16)
  (seen 21)
  (unrealized (0 1))
  (comment "3 in cohort - 2 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand owner-open 1 (k k) (n n-0) (d d) (o o))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((0 0) (5 0)) ((2 4) (3 1)) ((3 3) (1 0))
    ((4 0) (3 0)) ((5 1) (1 2)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 2 4)
    (trans 2 2) (trans 2 3) (trans 2 1) (no-state-split))
  (operation encryption-test (added-listener k) (enc "may I pass" k)
    (1 2))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load ls (cat pt-4 "st" d any))
      (load lk (cat pt-2 "st-k" d o k)) (stor ls (cat pt "st" d o o)))
    ((send (enc "open" d o n-0 k))) ((recv k) (send k)))
  (label 19)
  (parent 16)
  (seen 23)
  (unrealized (0 1) (5 0))
  (comment "4 in cohort - 1 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 4) (4 0)) ((3 3) (1 0)) ((4 1) (3 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 2 4)
    (trans 2 2) (trans 2 3) (trans 2 1) (no-state-split))
  (rule eff-dev-up-3)
  (operation nonce-test (displaced 5 2 dev-up 4) k (4 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load ls (cat pt-4 "st" d any))
      (load lk (cat pt-2 "st-k" d o k)) (stor ls (cat pt "st" d o o)))
    ((recv k) (send k)))
  (label 20)
  (parent 17)
  (seen 20)
  (unrealized (0 1) (4 0))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (any old old1 mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand owner-open 1 (k k) (n n-0) (d d) (o o))
  (defstrand user-pass 1 (k k))
  (defstrand dev-up 6 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (precedes ((0 0) (5 0)) ((2 3) (1 0)) ((3 0) (2 0)) ((4 0) (1 2))
    ((5 4) (2 1)) ((5 5) (0 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 2 3) (trans 2 1) (trans 5 4)
    (trans 5 2) (trans 5 3) (trans 5 1) (no-state-split))
  (operation encryption-test (displaced 2 6 dev-up 6) (enc "up" k)
    (0 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-3 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv (enc "open" d o n-0 k)) (load ls (cat pt-0 "st" d any))
      (load lk (cat pt-3 "st-k" d o k)) (stor ls (cat pt "st" d o o)))
    ((send (enc "open" d o n-0 k))) ((send (enc "may I pass" k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-1 old))
      (load ls (cat pt-2 old1)) (stor lk (cat pt-3 "st-k" d o k))
      (stor ls (cat pt-4 "st" d o)) (send (enc "up" k))))
  (label 21)
  (parent 18)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((k k) (d d) (o o) (start-ch start-ch) (n n) (d-0 d) (o-0 o)
        (lk lk) (ls ls) (pt pt-3) (pt-0 pt))))
  (origs (pt-3 (5 3)) (pt-4 (5 4)) (pt (2 3)) (n (1 3)) (k (0 0))))

(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand owner-open 1 (k k) (n n-0) (d d) (o o))
  (defstrand user-pass 1 (k k))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((0 0) (6 0)) ((2 4) (3 1)) ((3 3) (1 0))
    ((4 0) (3 0)) ((5 0) (1 2)) ((6 1) (0 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 2 4)
    (trans 2 2) (trans 2 3) (trans 2 1) (no-state-split))
  (operation encryption-test (added-listener k) (enc "up" k) (0 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load ls (cat pt-4 "st" d any))
      (load lk (cat pt-2 "st-k" d o k)) (stor ls (cat pt "st" d o o)))
    ((send (enc "open" d o n-0 k))) ((send (enc "may I pass" k)))
    ((recv k) (send k)))
  (label 22)
  (parent 18)
  (seen 24)
  (unrealized (6 0))
  (comment "8 in cohort - 1 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand owner-open 1 (k k) (n n-0) (d d) (o o))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 4) (3 1)) ((2 4) (5 0)) ((3 3) (1 0))
    ((4 0) (3 0)) ((5 1) (1 2)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 2 4)
    (trans 2 2) (trans 2 3) (trans 2 1) (no-state-split))
  (rule eff-dev-up-3)
  (operation nonce-test (displaced 6 2 dev-up 4) k (5 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load ls (cat pt-4 "st" d any))
      (load lk (cat pt-2 "st-k" d o k)) (stor ls (cat pt "st" d o o)))
    ((send (enc "open" d o n-0 k))) ((recv k) (send k)))
  (label 23)
  (parent 19)
  (seen 23)
  (unrealized (0 1) (5 0))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand owner-open 1 (k k) (n n-0) (d d) (o o))
  (defstrand user-pass 1 (k k))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 4) (3 1)) ((2 4) (6 0)) ((3 3) (1 0))
    ((4 0) (3 0)) ((5 0) (1 2)) ((6 1) (0 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o) (cat "st-k" d o k))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 2 4)
    (trans 2 2) (trans 2 3) (trans 2 1) (no-state-split))
  (rule eff-dev-up-3)
  (operation nonce-test (displaced 7 2 dev-up 4) k (6 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-2 "st-k" d o k)) (load ls (cat pt "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1)) (stor lk (cat pt-2 "st-k" d o k))
      (stor ls (cat pt-3 "st" d o)))
    ((recv (enc "open" d o n-0 k)) (load ls (cat pt-4 "st" d any))
      (load lk (cat pt-2 "st-k" d o k)) (stor ls (cat pt "st" d o o)))
    ((send (enc "open" d o n-0 k))) ((send (enc "may I pass" k)))
    ((recv k) (send k)))
  (label 24)
  (parent 22)
  (seen 24)
  (unrealized (6 0))
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")
