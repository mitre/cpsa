(herald open-closed (bound 44))

(comment "CPSA 4.3.1")
(comment "All input read from tst/open-closed.scm")
(comment "Strand count bounded at 44")

(defprotocol open-closed basic
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
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z 1) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z (cat o o)))
        (gen-st (cat "st" d o o)))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d o o)))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 2) (p "dev-up" z2 2) (p "dev-up" "k" z1 k)
          (p "dev-up" "k" z2 k))
        (= z2 z1))))
  (defrule same-locn
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (same-locn z1 i1 z2 i2) (fact ha z1 i1 z2 i2)))
    (comment this is a rule comment))
  (defrule leadsto-la
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (leads-to z1 i1 z2 i2) (fact la z1 i1 z2 i2)))
    (comment this is a rule comment))
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
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 4))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 3))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd)) (implies (p "dev-up" z 3) (trans z 2))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd)) (implies (p "dev-up" z 3) (trans z 1))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 3))))
  (defgenrule trRl_dev-open-at-2
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 2))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 3))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 2)))))

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

(defskeleton open-closed
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

(defskeleton open-closed
  (vars (old mesg) (k skey) (d o name) (pt pt-0 pval) (start-ch chan)
    (lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (deflistener k)
  (defstrand dev-up 3 (old old) (k k) (d d) (o o) (start-ch start-ch)
    (lk lk))
  (precedes ((0 0) (2 0)) ((2 2) (1 0)))
  (uniq-orig k)
  (conf start-ch)
  (auth start-ch)
  (facts (ha 2 1 2 1) (ha 2 1 2 2) (ha 2 2 2 1) (ha 2 2 2 2))
  (rule same-locn trRl_dev-up-at-1 trRl_dev-up-at-2)
  (operation nonce-test (added-strand dev-up 3) k (1 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv k) (send k))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt old))
      (stor lk (cat pt-0 "st-k" d o k))))
  (label 2)
  (parent 1)
  (seen 2)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol open-closed basic
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
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z 1) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z (cat o o)))
        (gen-st (cat "st" d o o)))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d o o)))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 2) (p "dev-up" z2 2) (p "dev-up" "k" z1 k)
          (p "dev-up" "k" z2 k))
        (= z2 z1))))
  (defrule same-locn
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (same-locn z1 i1 z2 i2) (fact ha z1 i1 z2 i2)))
    (comment this is a rule comment))
  (defrule leadsto-la
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (leads-to z1 i1 z2 i2) (fact la z1 i1 z2 i2)))
    (comment this is a rule comment))
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
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 4))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 3))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd)) (implies (p "dev-up" z 3) (trans z 2))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd)) (implies (p "dev-up" z 3) (trans z 1))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 3))))
  (defgenrule trRl_dev-open-at-2
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 2))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 3))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 2)))))

(defskeleton open-closed
  (vars (k skey) (n text) (d o name) (pt pt-0 pval) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (uniq-orig n)
  (traces
    ((load lk (cat pt "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d o o)) (send (enc "you may pass" n k))))
  (label 3)
  (realized)
  (origs (n (0 3)))
  (comment "Not closed under rules"))

(defskeleton open-closed
  (vars (k skey) (n text) (d o name) (pt pt-0 pval) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (uniq-orig n)
  (gen-st (cat "st" d o o))
  (facts (ha 0 0 0 0) (ha 0 2 0 2))
  (rule gen-state-pass same-locn)
  (traces
    ((load lk (cat pt "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d o o)) (send (enc "you may pass" n k))))
  (label 4)
  (parent 3)
  (unrealized (0 2))
  (origs (n (0 3)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton open-closed
  (vars (any mesg) (k k-0 skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pval) (lk ls lk-0 locn))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o) (lk lk-0)
    (ls ls))
  (precedes ((1 3) (0 2)))
  (uniq-orig n)
  (gen-st (cat "st" d o o))
  (facts (ha 0 0 0 0) (ha 0 2 0 2) (ha 0 2 1 2) (ha 0 2 1 3)
    (ha 1 0 1 0) (ha 1 2 0 2) (ha 1 2 1 2) (ha 1 2 1 3) (ha 1 3 0 2)
    (ha 1 3 1 2) (ha 1 3 1 3) (la 1 3 0 2))
  (rule leadsto-la same-locn trRl_dev-open-at-2 trRl_dev-open-at-3)
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
  (defrule gen-state-close
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-close" z 1) (p "dev-close" "d" z d)
          (p "dev-close" "o" z o) (p "dev-close" "k" z k)
          (p "dev-close" "any" z (cat o o)))
        (gen-st (cat "st" d o o)))))
  (defrule gen-state-pass
    (forall ((z strd) (d o name) (k skey))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "d" z d)
          (p "dev-pass" "o" z o) (p "dev-pass" "k" z k))
        (gen-st (cat "st" d o o)))))
  (defrule power-deliver-once
    (forall ((z1 z2 strd) (k skey))
      (implies
        (and (p "dev-up" z1 2) (p "dev-up" z2 2) (p "dev-up" "k" z1 k)
          (p "dev-up" "k" z2 k))
        (= z2 z1))))
  (defrule same-locn
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (same-locn z1 i1 z2 i2) (fact ha z1 i1 z2 i2)))
    (comment this is a rule comment))
  (defrule leadsto-la
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (leads-to z1 i1 z2 i2) (fact la z1 i1 z2 i2)))
    (comment this is a rule comment))
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
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 4))))
  (defgenrule trRl_dev-up-at-3
    (forall ((z strd)) (implies (p "dev-up" z 5) (trans z 3))))
  (defgenrule trRl_dev-up-at-2
    (forall ((z strd)) (implies (p "dev-up" z 3) (trans z 2))))
  (defgenrule trRl_dev-up-at-1
    (forall ((z strd)) (implies (p "dev-up" z 3) (trans z 1))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 3))))
  (defgenrule trRl_dev-open-at-2
    (forall ((z strd)) (implies (p "dev-open" z 4) (trans z 2))))
  (defgenrule trRl_dev-close-at-3
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 3))))
  (defgenrule trRl_dev-close-at-2
    (forall ((z strd)) (implies (p "dev-close" z 4) (trans z 2)))))

(defskeleton open-closed
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (uniq-orig k n)
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
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (precedes ((0 0) (1 0)))
  (uniq-orig k n)
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
  (vars (k skey) (n text) (d o d-0 o-0 name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (precedes ((0 0) (1 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d-0 o-0 o-0))
  (conf start-ch)
  (facts (ha 1 0 1 0) (ha 1 2 1 2))
  (rule gen-state-pass same-locn)
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
  (vars (old mesg) (k skey) (n text) (d o d-0 o-0 name)
    (pt pt-0 pt-1 pt-2 pval) (start-ch chan) (lk ls lk-0 locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d-0) (o o-0) (lk lk) (ls ls))
  (defstrand dev-up 3 (old old) (k k) (d d) (o o) (start-ch start-ch)
    (lk lk-0))
  (precedes ((0 0) (2 0)) ((2 2) (1 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d-0 o-0 o-0))
  (conf start-ch)
  (auth start-ch)
  (facts (ha 1 0 1 0) (ha 1 2 1 2) (ha 2 1 2 1) (ha 2 1 2 2)
    (ha 2 2 2 1) (ha 2 2 2 2))
  (rule same-locn trRl_dev-up-at-1 trRl_dev-up-at-2)
  (operation nonce-test (added-strand dev-up 3) k (1 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt "st-k" d-0 o-0 k)) (recv (enc "may I pass" k))
      (load ls (cat pt-0 "st" d-0 o-0 o-0))
      (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk-0 (cat pt-1 old))
      (stor lk-0 (cat pt-2 "st-k" d o k))))
  (label 9)
  (parent 8)
  (seen 9)
  (unrealized (0 1) (1 0) (1 1) (1 2))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton open-closed
  (vars (old mesg) (k skey) (n text) (d o name) (pt pt-0 pt-1 pval)
    (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 3 (old old) (k k) (d d) (o o) (start-ch start-ch)
    (lk lk))
  (precedes ((0 0) (2 0)) ((2 2) (1 0)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (ha 1 0 1 0) (ha 1 0 2 1) (ha 1 0 2 2) (ha 1 2 1 2)
    (ha 2 1 1 0) (ha 2 1 2 1) (ha 2 1 2 2) (ha 2 2 1 0) (ha 2 2 2 1)
    (ha 2 2 2 2) (la 2 2 1 0))
  (rule leadsto-la same-locn trRl_dev-up-at-1 trRl_dev-up-at-2)
  (operation nonce-test
    (contracted (d-0 d) (o-0 o) (lk-0 lk) (pt-2 pt-1)) k (1 0)
    (ch-msg start-ch (cat "power-up" d o k))
    (ch-msg lk (cat pt-1 "st-k" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-1 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k))))
  (label 10)
  (parent 9)
  (unrealized (0 1) (1 1) (1 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton open-closed
  (vars (old mesg) (k skey) (n text) (d o name) (pt pt-0 pt-1 pval)
    (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 3 (old old) (k k) (d d) (o o) (start-ch start-ch)
    (lk lk))
  (defstrand user-pass 1 (k k))
  (precedes ((0 0) (2 0)) ((2 2) (1 0)) ((3 0) (1 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (ha 1 0 1 0) (ha 1 0 2 1) (ha 1 0 2 2) (ha 1 2 1 2)
    (ha 2 1 1 0) (ha 2 1 2 1) (ha 2 1 2 2) (ha 2 2 1 0) (ha 2 2 2 1)
    (ha 2 2 2 2) (la 2 2 1 0))
  (rule leadsto-la same-locn trRl_dev-up-at-1 trRl_dev-up-at-2)
  (operation encryption-test (added-strand user-pass 1)
    (enc "may I pass" k) (1 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-1 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k))) ((send (enc "may I pass" k))))
  (label 11)
  (parent 10)
  (unrealized (0 1) (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton open-closed
  (vars (old mesg) (k skey) (n text) (d o name) (pt pt-0 pt-1 pval)
    (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 3 (old old) (k k) (d d) (o o) (start-ch start-ch)
    (lk lk))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((0 0) (3 0)) ((2 2) (1 0)) ((3 1) (1 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (ha 1 0 1 0) (ha 1 0 2 1) (ha 1 0 2 2) (ha 1 2 1 2)
    (ha 2 1 1 0) (ha 2 1 2 1) (ha 2 1 2 2) (ha 2 2 1 0) (ha 2 2 2 1)
    (ha 2 2 2 2) (la 2 2 1 0))
  (rule leadsto-la same-locn trRl_dev-up-at-1 trRl_dev-up-at-2)
  (operation encryption-test (added-listener k) (enc "may I pass" k)
    (1 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-1 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k))) ((recv k) (send k)))
  (label 12)
  (parent 10)
  (seen 14)
  (unrealized (0 1) (1 2) (3 0))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton open-closed
  (vars (old any mesg) (k k-0 skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (start-ch chan) (ls lk lk-0 locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 3 (old old) (k k) (d d) (o o) (start-ch start-ch)
    (lk lk))
  (defstrand user-pass 1 (k k))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o) (lk lk-0)
    (ls ls))
  (precedes ((0 0) (2 0)) ((2 2) (1 0)) ((3 0) (1 1)) ((4 3) (1 2)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (ha 1 0 1 0) (ha 1 0 2 1) (ha 1 0 2 2) (ha 1 2 1 2)
    (ha 1 2 4 2) (ha 1 2 4 3) (ha 2 1 1 0) (ha 2 1 2 1) (ha 2 1 2 2)
    (ha 2 2 1 0) (ha 2 2 2 1) (ha 2 2 2 2) (ha 4 0 4 0) (ha 4 2 1 2)
    (ha 4 2 4 2) (ha 4 2 4 3) (ha 4 3 1 2) (ha 4 3 4 2) (ha 4 3 4 3)
    (la 4 3 1 2) (la 2 2 1 0))
  (rule leadsto-la same-locn trRl_dev-open-at-2 trRl_dev-open-at-3
    trRl_dev-up-at-1 trRl_dev-up-at-2)
  (operation channel-test (added-strand dev-open 4)
    (ch-msg ls (cat pt "st" d o o)) (1 2))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-1 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k))) ((send (enc "may I pass" k)))
    ((load lk-0 (cat pt-2 "st-k" d o k-0))
      (recv (enc "open" d o n-0 k-0)) (load ls (cat pt-3 "st" d any))
      (stor ls (cat pt "st" d o o))))
  (label 13)
  (parent 11)
  (seen 15)
  (unrealized (0 1))
  (comment "3 in cohort - 2 not yet seen"))

(defskeleton open-closed
  (vars (old mesg) (k skey) (n text) (d o name) (pt pt-0 pt-1 pval)
    (start-ch chan) (ls lk locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 3 (old old) (k k) (d d) (o o) (start-ch start-ch)
    (lk lk))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 2) (1 0)) ((2 2) (3 0)) ((3 1) (1 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (ha 1 0 1 0) (ha 1 0 2 1) (ha 1 0 2 2) (ha 1 2 1 2)
    (ha 2 1 1 0) (ha 2 1 2 1) (ha 2 1 2 2) (ha 2 2 1 0) (ha 2 2 2 1)
    (ha 2 2 2 2) (la 2 2 1 0))
  (rule leadsto-la same-locn trRl_dev-up-at-1 trRl_dev-up-at-2)
  (operation nonce-test (displaced 4 2 dev-up 3) k (3 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-1 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k))) ((recv k) (send k)))
  (label 14)
  (parent 12)
  (seen 14)
  (unrealized (0 1) (1 2) (3 0))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton open-closed
  (vars (any old old1 mesg) (k k-0 skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval) (start-ch chan)
    (ls lk lk-0 ls-0 locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk-0) (ls ls))
  (defstrand user-pass 1 (k k))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o) (lk lk)
    (ls ls))
  (defstrand dev-up 6 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk-0) (ls ls-0))
  (precedes ((0 0) (4 0)) ((2 0) (1 1)) ((3 3) (1 2)) ((4 2) (1 0))
    ((4 5) (0 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (ha 1 0 1 0) (ha 1 0 4 1) (ha 1 0 4 2) (ha 1 2 1 2)
    (ha 1 2 3 2) (ha 1 2 3 3) (ha 3 0 3 0) (ha 3 2 1 2) (ha 3 2 3 2)
    (ha 3 2 3 3) (ha 3 3 1 2) (ha 3 3 3 2) (ha 3 3 3 3) (ha 4 1 1 0)
    (ha 4 1 4 1) (ha 4 1 4 2) (ha 4 2 1 0) (ha 4 2 4 1) (ha 4 2 4 2)
    (ha 4 3 4 3) (ha 4 3 4 4) (ha 4 4 4 3) (ha 4 4 4 4) (la 4 2 1 0)
    (la 3 3 1 2))
  (rule leadsto-la same-locn trRl_dev-open-at-2 trRl_dev-open-at-3
    trRl_dev-up-at-1 trRl_dev-up-at-2 trRl_dev-up-at-3 trRl_dev-up-at-4)
  (operation encryption-test (displaced 2 5 dev-up 6) (enc "up" k)
    (0 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk-0 (cat pt-3 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((send (enc "may I pass" k)))
    ((load lk (cat pt-0 "st-k" d o k-0)) (recv (enc "open" d o n-0 k-0))
      (load ls (cat pt-1 "st" d any)) (stor ls (cat pt "st" d o o)))
    ((recv start-ch (cat "power-up" d o k)) (load lk-0 (cat pt-2 old))
      (stor lk-0 (cat pt-3 "st-k" d o k)) (load ls-0 (cat pt-4 old1))
      (stor ls-0 (cat pt-5 "st" d o)) (send (enc "up" k))))
  (label 15)
  (parent 13)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((k k) (d d) (o o) (start-ch start-ch) (n n) (d-0 d) (o-0 o)
        (lk lk-0) (ls ls))))
  (origs (pt-3 (4 2)) (pt-5 (4 4)) (pt (3 3)) (n (1 3)) (k (0 0))))

(defskeleton open-closed
  (vars (old any mesg) (k k-0 skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (start-ch chan) (ls lk lk-0 locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 3 (old old) (k k) (d d) (o o) (start-ch start-ch)
    (lk lk))
  (defstrand user-pass 1 (k k))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o) (lk lk-0)
    (ls ls))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((0 0) (5 0)) ((2 2) (1 0)) ((3 0) (1 1))
    ((4 3) (1 2)) ((5 1) (0 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (ha 1 0 1 0) (ha 1 0 2 1) (ha 1 0 2 2) (ha 1 2 1 2)
    (ha 1 2 4 2) (ha 1 2 4 3) (ha 2 1 1 0) (ha 2 1 2 1) (ha 2 1 2 2)
    (ha 2 2 1 0) (ha 2 2 2 1) (ha 2 2 2 2) (ha 4 0 4 0) (ha 4 2 1 2)
    (ha 4 2 4 2) (ha 4 2 4 3) (ha 4 3 1 2) (ha 4 3 4 2) (ha 4 3 4 3)
    (la 4 3 1 2) (la 2 2 1 0))
  (rule leadsto-la same-locn trRl_dev-open-at-2 trRl_dev-open-at-3
    trRl_dev-up-at-1 trRl_dev-up-at-2)
  (operation encryption-test (added-listener k) (enc "up" k) (0 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-1 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k))) ((send (enc "may I pass" k)))
    ((load lk-0 (cat pt-2 "st-k" d o k-0))
      (recv (enc "open" d o n-0 k-0)) (load ls (cat pt-3 "st" d any))
      (stor ls (cat pt "st" d o o))) ((recv k) (send k)))
  (label 16)
  (parent 13)
  (seen 17)
  (unrealized (5 0))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton open-closed
  (vars (old any mesg) (k k-0 skey) (n n-0 text) (d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (start-ch chan) (ls lk lk-0 locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (d d) (o o) (lk lk) (ls ls))
  (defstrand dev-up 3 (old old) (k k) (d d) (o o) (start-ch start-ch)
    (lk lk))
  (defstrand user-pass 1 (k k))
  (defstrand dev-open 4 (any any) (k k-0) (n n-0) (d d) (o o) (lk lk-0)
    (ls ls))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 2) (1 0)) ((2 2) (5 0)) ((3 0) (1 1))
    ((4 3) (1 2)) ((5 1) (0 1)))
  (uniq-orig k n)
  (gen-st (cat "st" d o o))
  (conf start-ch)
  (auth start-ch)
  (facts (ha 1 0 1 0) (ha 1 0 2 1) (ha 1 0 2 2) (ha 1 2 1 2)
    (ha 1 2 4 2) (ha 1 2 4 3) (ha 2 1 1 0) (ha 2 1 2 1) (ha 2 1 2 2)
    (ha 2 2 1 0) (ha 2 2 2 1) (ha 2 2 2 2) (ha 4 0 4 0) (ha 4 2 1 2)
    (ha 4 2 4 2) (ha 4 2 4 3) (ha 4 3 1 2) (ha 4 3 4 2) (ha 4 3 4 3)
    (la 4 3 1 2) (la 2 2 1 0))
  (rule leadsto-la same-locn trRl_dev-open-at-2 trRl_dev-open-at-3
    trRl_dev-up-at-1 trRl_dev-up-at-2)
  (operation nonce-test (displaced 6 2 dev-up 3) k (5 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-1 "st-k" d o k)) (recv (enc "may I pass" k))
      (load ls (cat pt "st" d o o)) (send (enc "you may pass" n k)))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (stor lk (cat pt-1 "st-k" d o k))) ((send (enc "may I pass" k)))
    ((load lk-0 (cat pt-2 "st-k" d o k-0))
      (recv (enc "open" d o n-0 k-0)) (load ls (cat pt-3 "st" d any))
      (stor ls (cat pt "st" d o o))) ((recv k) (send k)))
  (label 17)
  (parent 16)
  (seen 17)
  (unrealized (5 0))
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")
