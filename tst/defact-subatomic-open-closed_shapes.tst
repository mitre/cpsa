(comment "CPSA 4.4.5")
(comment "Extracted shapes")

(herald subatomic-open-closed (bound 40))

(comment "CPSA 4.4.5")

(comment "All input read from tst/subatomic-open-closed.scm")

(comment "Strand count bounded at 40")

(defprotocol subatomic-open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (load ls old1) (stor lk (cat "st-k" d o k))
      (stor ls (cat "st" d o)) (send (enc "up" k)))
    (auth start-ch)
    (critical-sections (1 4)))
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
    (gen-st (cat "st-k" d o k) (cat "st" d (cat o o))))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (recv (enc "close" d o n k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o)) (send n))
    (gen-st (cat "st-k" d o k))
    (critical-sections (1 3)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (load ls (cat "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    (uniq-orig n)
    (gen-st (cat "st-k" d o k) (cat "st" d (cat o o)))
    (critical-sections (0 1)))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 (idx 2)) (p "dev-up" z2 (idx 2))
          (p "dev-up" "k" z1 k) (p "dev-up" "k" z2 k))
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
  (defgenrule discreteAfter
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule discreteBefore
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule fact-dev-up-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-up" z (idx 3)) (p "dev-up" "ls" z ls)
          (p "dev-up" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule fact-dev-open-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-open" z (idx 3)) (p "dev-open" "ls" z ls)
          (p "dev-open" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule fact-dev-close-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-close" z (idx 3)) (p "dev-close" "ls" z ls)
          (p "dev-close" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule fact-dev-pass-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-pass" z (idx 2)) (p "dev-pass" "ls" z ls)
          (p "dev-pass" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-up-at-4
    (forall ((z strd))
      (implies (p "dev-up" z (idx 5)) (trans z (idx 4)))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd))
      (implies (p "dev-up" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd))
      (implies (p "dev-up" z (idx 5)) (trans z (idx 2)))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd))
      (implies (p "dev-up" z (idx 4)) (trans z (idx 1)))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-open-at-1
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 1)))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd))
      (implies (p "dev-close" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd))
      (implies (p "dev-close" z (idx 4)) (trans z (idx 2)))))
  (defgenrule eff-dev-up-3
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-up" z (idx 4)) (prec z (idx 3) z1 i))
        (or (= z z1)
          (and (p "dev-up" z (idx 5)) (prec z (idx 4) z1 i))))))
  (defgenrule cau-dev-up-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-up" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-open-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-open" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-close-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-close" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-pass-1
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-pass" z (idx 2)) (prec z1 i z (idx 1)))
        (or (= z z1) (prec z1 i z (idx 0))))))
  (defgenrule gen-st-dev-open-1
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-open" z (idx 1)) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (d o name))
      (implies
        (and (p "dev-open" z (idx 1)) (p "dev-open" "o" z o)
          (p "dev-open" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule gen-st-dev-close-0
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z (idx 1)) (p "dev-close" "k" z k)
          (p "dev-close" "o" z o) (p "dev-close" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (d o name))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "o" z o)
          (p "dev-pass" "d" z d)) (gen-st (cat "st" d o o))))))

(defskeleton subatomic-open-closed
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

(comment "Nothing left to do")

(defprotocol subatomic-open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (load ls old1) (stor lk (cat "st-k" d o k))
      (stor ls (cat "st" d o)) (send (enc "up" k)))
    (auth start-ch)
    (critical-sections (1 4)))
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
    (gen-st (cat "st-k" d o k) (cat "st" d (cat o o))))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (recv (enc "close" d o n k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o)) (send n))
    (gen-st (cat "st-k" d o k))
    (critical-sections (1 3)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (load ls (cat "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    (uniq-orig n)
    (gen-st (cat "st-k" d o k) (cat "st" d (cat o o)))
    (critical-sections (0 1)))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 (idx 2)) (p "dev-up" z2 (idx 2))
          (p "dev-up" "k" z1 k) (p "dev-up" "k" z2 k))
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
  (defgenrule discreteAfter
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule discreteBefore
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule fact-dev-up-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-up" z (idx 3)) (p "dev-up" "ls" z ls)
          (p "dev-up" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule fact-dev-open-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-open" z (idx 3)) (p "dev-open" "ls" z ls)
          (p "dev-open" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule fact-dev-close-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-close" z (idx 3)) (p "dev-close" "ls" z ls)
          (p "dev-close" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule fact-dev-pass-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-pass" z (idx 2)) (p "dev-pass" "ls" z ls)
          (p "dev-pass" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-up-at-4
    (forall ((z strd))
      (implies (p "dev-up" z (idx 5)) (trans z (idx 4)))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd))
      (implies (p "dev-up" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd))
      (implies (p "dev-up" z (idx 5)) (trans z (idx 2)))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd))
      (implies (p "dev-up" z (idx 4)) (trans z (idx 1)))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-open-at-1
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 1)))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd))
      (implies (p "dev-close" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd))
      (implies (p "dev-close" z (idx 4)) (trans z (idx 2)))))
  (defgenrule eff-dev-up-3
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-up" z (idx 4)) (prec z (idx 3) z1 i))
        (or (= z z1)
          (and (p "dev-up" z (idx 5)) (prec z (idx 4) z1 i))))))
  (defgenrule cau-dev-up-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-up" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-open-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-open" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-close-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-close" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-pass-1
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-pass" z (idx 2)) (prec z1 i z (idx 1)))
        (or (= z z1) (prec z1 i z (idx 0))))))
  (defgenrule gen-st-dev-open-1
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-open" z (idx 1)) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (d o name))
      (implies
        (and (p "dev-open" z (idx 1)) (p "dev-open" "o" z o)
          (p "dev-open" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule gen-st-dev-close-0
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z (idx 1)) (p "dev-close" "k" z k)
          (p "dev-close" "o" z o) (p "dev-close" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (d o name))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "o" z o)
          (p "dev-pass" "d" z d)) (gen-st (cat "st" d o o))))))

(defskeleton subatomic-open-closed
  (vars (k skey) (n text) (d o name) (pt pt-0 pval) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (uniq-orig n)
  (traces
    ((load lk (cat pt "st-k" d o k)) (load ls (cat pt-0 "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k))))
  (label 3)
  (realized)
  (origs (n (0 3)))
  (comment "Not closed under rules"))

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
  (leads-to ((1 3) (0 0)) ((1 3) (3 2)) ((3 3) (0 1)))
  (operation channel-test (displaced 4 1 dev-up 4)
    (ch-msg lk (cat pt-5 "st-k" d o k-0)) (3 2))
  (strand-map 0 1 2 3)
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
  (parent 3)
  (realized)
  (shape)
  (maps ((0) ((k k) (n n) (d d) (o o) (lk lk) (ls ls))))
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
    (critical-sections (1 4)))
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
    (gen-st (cat "st-k" d o k) (cat "st" d (cat o o))))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (recv (enc "close" d o n k)) (load lk (cat "st-k" d o k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d o)) (send n))
    (gen-st (cat "st-k" d o k))
    (critical-sections (1 3)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (load ls (cat "st" d o o))
      (recv (enc "may I pass" k)) (send (enc "you may pass" n k)))
    (uniq-orig n)
    (gen-st (cat "st-k" d o k) (cat "st" d (cat o o)))
    (critical-sections (0 1)))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 (idx 2)) (p "dev-up" z2 (idx 2))
          (p "dev-up" "k" z1 k) (p "dev-up" "k" z2 k))
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
  (defgenrule discreteAfter
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule discreteBefore
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule fact-dev-up-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-up" z (idx 3)) (p "dev-up" "ls" z ls)
          (p "dev-up" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule fact-dev-open-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-open" z (idx 3)) (p "dev-open" "ls" z ls)
          (p "dev-open" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule fact-dev-close-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-close" z (idx 3)) (p "dev-close" "ls" z ls)
          (p "dev-close" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule fact-dev-pass-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-pass" z (idx 2)) (p "dev-pass" "ls" z ls)
          (p "dev-pass" "lk" z lk)) (fact same-dev ls lk))))
  (defgenrule trRl_dev-up-at-4
    (forall ((z strd))
      (implies (p "dev-up" z (idx 5)) (trans z (idx 4)))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd))
      (implies (p "dev-up" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd))
      (implies (p "dev-up" z (idx 5)) (trans z (idx 2)))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd))
      (implies (p "dev-up" z (idx 4)) (trans z (idx 1)))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-open-at-1
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 1)))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd))
      (implies (p "dev-close" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd))
      (implies (p "dev-close" z (idx 4)) (trans z (idx 2)))))
  (defgenrule eff-dev-up-3
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-up" z (idx 4)) (prec z (idx 3) z1 i))
        (or (= z z1)
          (and (p "dev-up" z (idx 5)) (prec z (idx 4) z1 i))))))
  (defgenrule cau-dev-up-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-up" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-open-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-open" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-close-2
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-close" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-pass-1
    (forall ((i indx) (z1 z strd))
      (implies (and (p "dev-pass" z (idx 2)) (prec z1 i z (idx 1)))
        (or (= z z1) (prec z1 i z (idx 0))))))
  (defgenrule gen-st-dev-open-1
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-open" z (idx 1)) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (d o name))
      (implies
        (and (p "dev-open" z (idx 1)) (p "dev-open" "o" z o)
          (p "dev-open" "d" z d)) (gen-st (cat "st" d o o)))))
  (defgenrule gen-st-dev-close-0
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z (idx 1)) (p "dev-close" "k" z k)
          (p "dev-close" "o" z o) (p "dev-close" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (cat "st-k" d o k)))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (d o name))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "o" z o)
          (p "dev-pass" "d" z d)) (gen-st (cat "st" d o o))))))

(defskeleton subatomic-open-closed
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (uniq-orig k n)
  (conf start-ch)
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
  (leads-to ((2 3) (1 1)) ((5 3) (1 0)) ((5 3) (2 2)))
  (operation encryption-test (displaced 2 6 dev-up 6) (enc "up" k)
    (0 1))
  (strand-map 0 1 5 2 3 4)
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
  (parent 9)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((k k) (d d) (o o) (start-ch start-ch) (n n) (d-0 d) (o-0 o)
        (lk lk) (ls ls))))
  (origs (pt-3 (5 3)) (pt-4 (5 4)) (pt (2 3)) (n (1 3)) (k (0 0))))

(comment "Nothing left to do")
