(comment "CPSA 4.4.5")
(comment "Extracted shapes")

(herald open-closed (bound 44))

(comment "CPSA 4.4.5")

(comment "All input read from tst/open-closed-tag.scm")

(comment "Strand count bounded at 44")

(defprotocol open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (stor lk (cat "st-k" d o k)) (load ls old1)
      (stor ls (cat "st" d "closed")) (send (enc "up" k)))
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
      (load ls (cat "st" d any)) (stor ls (cat "st" d "opened"))
      (send n)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "close" d o n k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d "closed"))
      (send n)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat "st" d "opened")) (send (enc "you may pass" n k)))
    (uniq-orig n))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z (idx 1)) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z "opened"))
        (gen-st (cat "st" d "opened")))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d "opened")))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 (idx 2)) (p "dev-up" z2 (idx 2))
          (p "dev-up" "k" z1 k) (p "dev-up" "k" z2 k))
        (= z1 z2))))
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
      (implies (p "dev-close" z (idx 4)) (trans z (idx 2))))))

(defskeleton open-closed
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

(defprotocol open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (stor lk (cat "st-k" d o k)) (load ls old1)
      (stor ls (cat "st" d "closed")) (send (enc "up" k)))
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
      (load ls (cat "st" d any)) (stor ls (cat "st" d "opened"))
      (send n)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "close" d o n k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d "closed"))
      (send n)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat "st" d "opened")) (send (enc "you may pass" n k)))
    (uniq-orig n))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z (idx 1)) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z "opened"))
        (gen-st (cat "st" d "opened")))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d "opened")))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 (idx 2)) (p "dev-up" z2 (idx 2))
          (p "dev-up" "k" z1 k) (p "dev-up" "k" z2 k))
        (= z1 z2))))
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
      (implies (p "dev-close" z (idx 4)) (trans z (idx 2))))))

(defskeleton open-closed
  (vars (k skey) (n text) (d o name) (pt pt-0 pval) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (uniq-orig n)
  (traces
    ((load lk (cat pt "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d "opened"))
      (send (enc "you may pass" n k))))
  (label 3)
  (realized)
  (origs (n (0 3)))
  (comment "Not closed under rules"))

(defskeleton open-closed
  (vars (any mesg) (k k-0 skey) (n n-0 text) (d o o-0 name)
    (pt pt-0 pt-1 pt-2 pval) (lk ls lk-0 locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o-0)
    (lk lk-0) (ls ls))
  (precedes ((1 3) (0 2)))
  (uniq-orig n)
  (gen-st (cat "st" d "opened"))
  (leads-to ((1 3) (0 2)))
  (operation channel-test (added-strand dev-open 4)
    (ch-msg ls (cat pt-0 "st" d "opened")) (0 2))
  (strand-map 0)
  (traces
    ((load lk (cat pt "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d "opened"))
      (send (enc "you may pass" n k)))
    ((load lk-0 (cat pt-1 "st-k" d o-0 k-0))
      (recv (enc "open" d o-0 n-0 k-0)) (load ls (cat pt-2 "st" d any))
      (stor ls (cat pt-0 "st" d "opened"))))
  (label 5)
  (parent 3)
  (realized)
  (shape)
  (maps ((0) ((k k) (n n) (d d) (o o) (lk lk) (ls ls))))
  (origs (pt-0 (1 3)) (n (0 3))))

(comment "Nothing left to do")

(defprotocol open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (stor lk (cat "st-k" d o k)) (load ls old1)
      (stor ls (cat "st" d "closed")) (send (enc "up" k)))
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
      (load ls (cat "st" d any)) (stor ls (cat "st" d "opened"))
      (send n)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "close" d o n k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d "closed"))
      (send n)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat "st" d "opened")) (send (enc "you may pass" n k)))
    (uniq-orig n))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z (idx 1)) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z "opened"))
        (gen-st (cat "st" d "opened")))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d "opened")))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 (idx 2)) (p "dev-up" z2 (idx 2))
          (p "dev-up" "k" z1 k) (p "dev-up" "k" z2 k))
        (= z1 z2))))
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
      (implies (p "dev-close" z (idx 4)) (trans z (idx 2))))))

(defskeleton open-closed
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (uniq-orig k n)
  (conf start-ch)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt "st-k" d-0 o-0 k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d-0 "opened"))
      (send (enc "you may pass" n k))))
  (label 6)
  (unrealized (0 1) (1 0) (1 1))
  (preskeleton)
  (origs (n (1 3)) (k (0 0)))
  (comment "Not a skeleton"))

(defskeleton open-closed
  (vars (any old old1 mesg) (k k-0 skey) (n n-0 text) (o d o-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval) (start-ch chan)
    (ls lk lk-0 ls-0 locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o-0) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o-0) (lk lk-0) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand dev-up 6 (old old) (old1 old1) (k k) (d d) (o o-0)
    (start-ch start-ch) (lk lk-0) (ls ls-0))
  (precedes ((0 0) (4 0)) ((2 0) (1 1)) ((3 3) (1 2)) ((4 2) (1 0))
    ((4 5) (0 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d "opened"))
  (conf start-ch)
  (auth start-ch)
  (leads-to ((3 3) (1 2)) ((4 2) (1 0)))
  (operation encryption-test (displaced 2 5 dev-up 6) (enc "up" k)
    (0 1))
  (strand-map 0 1 4 2 3)
  (traces ((send start-ch (cat "power-up" d o-0 k)) (recv (enc "up" k)))
    ((load lk-0 (cat pt-3 "st-k" d o-0 k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d "opened"))
      (send (enc "you may pass" n k))) ((send (enc "may I pass" k)))
    ((load lk (cat pt-0 "st-k" d o k-0)) (recv (enc "open" d o n-0 k-0))
      (load ls (cat pt-1 "st" d any))
      (stor ls (cat pt "st" d "opened")))
    ((recv start-ch (cat "power-up" d o-0 k)) (load lk-0 (cat pt-2 old))
      (stor lk-0 (cat pt-3 "st-k" d o-0 k)) (load ls-0 (cat pt-4 old1))
      (stor ls-0 (cat pt-5 "st" d "closed")) (send (enc "up" k))))
  (label 15)
  (parent 6)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((k k) (d d) (o o-0) (start-ch start-ch) (n n) (d-0 d) (o-0 o-0)
        (lk lk-0) (ls ls))))
  (origs (pt-3 (4 2)) (pt-5 (4 4)) (pt (3 3)) (n (1 3)) (k (0 0))))

(comment "Nothing left to do")

(defprotocol open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (stor lk (cat "st-k" d o k)) (load ls old1)
      (stor ls (cat "st" d "closed")) (send (enc "up" k)))
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
      (load ls (cat "st" d any)) (stor ls (cat "st" d "opened"))
      (send n)))
  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "close" d o n k))
      (load ls (cat "st" d any)) (stor ls (cat "st" d "closed"))
      (send n)))
  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace (load lk (cat "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat "st" d "opened")) (send (enc "you may pass" n k)))
    (uniq-orig n))
  (defrole user-pass
    (vars (k skey))
    (trace (send (enc "may I pass" k)) (recv (enc "you may pass" k))))
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z (idx 1)) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z "opened"))
        (gen-st (cat "st" d "opened")))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d "opened")))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 (idx 2)) (p "dev-up" z2 (idx 2))
          (p "dev-up" "k" z1 k) (p "dev-up" "k" z2 k))
        (= z1 z2))))
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
      (implies (p "dev-close" z (idx 4)) (trans z (idx 2))))))

(defskeleton open-closed
  (vars (old old1 any mesg) (k k-0 skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval) (start-ch chan)
    (ls lk ls-0 lk-0 locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 6 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls-0))
  (defstrand user-pass 1 (k k))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o) (lk lk-0)
    (ls ls))
  (precedes ((0 0) (2 0)) ((2 2) (1 0)) ((2 5) (0 1)) ((3 0) (1 1))
    ((4 3) (1 2)))
  (uniq-orig k n)
  (conf start-ch)
  (auth start-ch)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d "opened"))
      (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-1 old))
      (stor lk (cat pt-2 "st-k" d o k)) (load ls-0 (cat pt-3 old1))
      (stor ls-0 (cat pt-4 "st" d "closed")) (send (enc "up" k)))
    ((send (enc "may I pass" k)))
    ((load lk-0 (cat pt-5 "st-k" d o k-0))
      (recv (enc "open" d o n-0 k-0)) (load ls (cat pt-6 "st" d any))
      (stor ls (cat pt-7 "st" d "opened"))))
  (label 18)
  (unrealized (1 0))
  (origs (pt-7 (4 3)) (pt-4 (2 4)) (pt-2 (2 2)) (n (1 3)) (k (0 0)))
  (comment "Not closed under rules"))

(defskeleton open-closed
  (vars (old old1 any mesg) (k k-0 skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval) (start-ch chan)
    (ls lk ls-0 lk-0 locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 6 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls-0))
  (defstrand user-pass 1 (k k))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o) (lk lk-0)
    (ls ls))
  (precedes ((0 0) (2 0)) ((2 2) (1 0)) ((2 5) (0 1)) ((3 0) (1 1))
    ((4 3) (1 2)))
  (uniq-orig k n)
  (gen-st (cat "st" d "opened"))
  (conf start-ch)
  (auth start-ch)
  (leads-to ((2 2) (1 0)) ((4 3) (1 2)))
  (operation channel-test (displaced 5 4 dev-open 4)
    (ch-msg ls (cat pt-6 "st" d "opened")) (1 2))
  (strand-map 0 1 2 3 4)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-0 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt-5 "st" d "opened"))
      (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt old))
      (stor lk (cat pt-0 "st-k" d o k)) (load ls-0 (cat pt-1 old1))
      (stor ls-0 (cat pt-2 "st" d "closed")) (send (enc "up" k)))
    ((send (enc "may I pass" k)))
    ((load lk-0 (cat pt-3 "st-k" d o k-0))
      (recv (enc "open" d o n-0 k-0)) (load ls (cat pt-4 "st" d any))
      (stor ls (cat pt-5 "st" d "opened"))))
  (label 21)
  (parent 18)
  (realized)
  (shape)
  (maps
    ((0 1 2 3 4)
      ((old old) (old1 old1) (any any) (n n) (n-0 n-0) (d d) (o o) (k k)
        (k-0 k-0) (start-ch start-ch) (ls ls) (lk lk) (ls-0 ls-0)
        (lk-0 lk-0))))
  (origs (pt-5 (4 3)) (pt-2 (2 4)) (pt-0 (2 2)) (n (1 3)) (k (0 0))))

(comment "Nothing left to do")
