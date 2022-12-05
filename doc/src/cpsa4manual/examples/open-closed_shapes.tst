(comment "CPSA 4.3.1")
(comment "Extracted shapes")

(herald open-closed-alt (bound 40))

(comment "CPSA 4.3.1")

(comment "All input read from open-closed.scm")

(comment "Strand count bounded at 40")

(defprotocol open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (load ls old1) (stor lk (dev-key-state d o k))
      (stor ls (door-state d (closed o))) (send (enc "up" k)))
    (auth start-ch)
    (facts (same-dev ls lk)))
  (defrole owner-power-dev
    (vars (k skey) (d o name) (start-ch chan))
    (trace (send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    (conf start-ch))
  (defrole owner-delg-key
    (vars (k skey) (n nb text) (d o b name) (to-b from-b chan))
    (trace (recv from-b (cat "req-key" b nb))
      (send to-b (delegate b d o nb n (hash-dk b nb n k)))
      (recv (hash b nb n)))
    (uniq-orig n)
    (conf to-b)
    (auth from-b))
  (defrole passer-recv-key
    (vars (kp ign mesg) (n nb text) (d o b name) (to-b from-b chan)
      (del-key-locn locn))
    (trace (send from-b (cat "req-key" b nb))
      (recv to-b (delegate b d o nb n kp)) (send (hash b nb n))
      (load del-key-locn ign)
      (stor del-key-locn (key-rec b d o nb n kp)))
    (uniq-orig nb)
    (auth to-b))
  (defrole passer-open
    (vars (kp mesg) (n nb text) (d o b name) (del-key-locn locn))
    (trace (load del-key-locn (key-rec b d o nb n kp))
      (send (cat b n (enc (open-req b d o nb n) kp)))
      (recv (hash (open-req b d o nb n)))))
  (defrole passer-close
    (vars (kp mesg) (n nb text) (d o b name) (del-key-locn locn))
    (trace (load del-key-locn (key-rec b d o nb n kp))
      (send (cat b n (enc (close-req b d o nb n) kp)))
      (recv (hash (close-req b d o nb n)))))
  (defrole dev-open
    (vars (k skey) (n nb text) (any mesg) (d o b name) (lk ls locn))
    (trace (load lk (dev-key-state d o k))
      (recv (cat b n (enc (open-req b d o nb n) (hash-dk b nb n k))))
      (load ls (door-state d any)) (load lk (dev-key-state d o k))
      (stor ls (door-state d (opened b nb n)))
      (send (hash (open-req b d o nb n))))
    (gen-st (dev-key-state d o k))
    (facts (same-dev ls lk)))
  (defrole dev-closed
    (vars (k skey) (n nb text) (any mesg) (d o b name) (lk ls locn))
    (trace (load lk (dev-key-state d o k))
      (recv (cat b n (enc (close-req b d o nb n) (hash-dk b nb n k))))
      (load ls (door-state d any)) (load lk (dev-key-state d o k))
      (stor ls (door-state d (closed o)))
      (send (hash (close-req b d o nb n))))
    (gen-st (dev-key-state d o k))
    (facts (same-dev ls lk)))
  (defrole dev-pass
    (vars (k skey) (n nb text) (d o b name) (lk ls locn))
    (trace (load lk (dev-key-state d o k))
      (load ls (door-state d (opened b nb n)))
      (recv (cat b nb n (enc "may I pass" (hash-dk b nb n k))))
      (send (enc "you may pass" n (hash-dk b nb n k))))
    (gen-st (dev-key-state d o k) (door-state d (opened b nb n)))
    (facts (same-dev ls lk)))
  (defrole passer-pass
    (vars (kp mesg) (n nb text) (d o b name) (del-key-locn locn))
    (trace (load del-key-locn (key-rec b d o nb n kp))
      (send (cat b nb n (enc "may I pass" kp)))
      (recv (enc "you may pass" kp))))
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
  (defgenrule fact-dev-closed-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-closed" z 3) (p "dev-closed" "lk" z lk)
          (p "dev-closed" "ls" z ls)) (fact same-dev ls lk))))
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
  (defgenrule trRl_passer-recv-key-at-4
    (forall ((z strd)) (implies (p "passer-recv-key" z 5) (trans z 4))))
  (defgenrule trRl_passer-recv-key-at-3
    (forall ((z strd)) (implies (p "passer-recv-key" z 5) (trans z 3))))
  (defgenrule trRl_dev-open-at-4
    (forall ((z strd)) (implies (p "dev-open" z 5) (trans z 4))))
  (defgenrule trRl_dev-open-at-2
    (forall ((z strd)) (implies (p "dev-open" z 5) (trans z 2))))
  (defgenrule trRl_dev-closed-at-4
    (forall ((z strd)) (implies (p "dev-closed" z 5) (trans z 4))))
  (defgenrule trRl_dev-closed-at-2
    (forall ((z strd)) (implies (p "dev-closed" z 5) (trans z 2))))
  (defgenrule eff-dev-up-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 4) (prec z 3 z1 i))
        (or (= z z1) (and (p "dev-up" z 5) (prec z 4 z1 i))))))
  (defgenrule cau-dev-up-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-open-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-open" z 4) (prec z1 i z 3))
        (or (= z z1) (prec z1 i z 2)))))
  (defgenrule cau-dev-closed-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-closed" z 4) (prec z1 i z 3))
        (or (= z z1) (prec z1 i z 2)))))
  (defgenrule cau-dev-pass-1
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-pass" z 2) (prec z1 i z 1))
        (or (= z z1) (prec z1 i z 0)))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-closed-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-closed" z 1) (p "dev-closed" "k" z k)
          (p "dev-closed" "o" z o) (p "dev-closed" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (n nb text) (b d name))
      (implies
        (and (p "dev-pass" z 2) (p "dev-pass" "n" z n)
          (p "dev-pass" "nb" z nb) (p "dev-pass" "b" z b)
          (p "dev-pass" "d" z d))
        (gen-st (door-state d (opened b nb n))))))
  (lang (closed (tuple 1)) (opened (tuple 3)) (door-state (tuple 2))
    (dev-key-state (tuple 3)) (open-req (tuple 5)) (close-req (tuple 5))
    (key-rec (tuple 6)) (delegate (tuple 6)) (hash-dk hash)))

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
      (load ls old1) (stor lk (dev-key-state d o k))
      (stor ls (door-state d (closed o))) (send (enc "up" k)))
    (auth start-ch)
    (facts (same-dev ls lk)))
  (defrole owner-power-dev
    (vars (k skey) (d o name) (start-ch chan))
    (trace (send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    (conf start-ch))
  (defrole owner-delg-key
    (vars (k skey) (n nb text) (d o b name) (to-b from-b chan))
    (trace (recv from-b (cat "req-key" b nb))
      (send to-b (delegate b d o nb n (hash-dk b nb n k)))
      (recv (hash b nb n)))
    (uniq-orig n)
    (conf to-b)
    (auth from-b))
  (defrole passer-recv-key
    (vars (kp ign mesg) (n nb text) (d o b name) (to-b from-b chan)
      (del-key-locn locn))
    (trace (send from-b (cat "req-key" b nb))
      (recv to-b (delegate b d o nb n kp)) (send (hash b nb n))
      (load del-key-locn ign)
      (stor del-key-locn (key-rec b d o nb n kp)))
    (uniq-orig nb)
    (auth to-b))
  (defrole passer-open
    (vars (kp mesg) (n nb text) (d o b name) (del-key-locn locn))
    (trace (load del-key-locn (key-rec b d o nb n kp))
      (send (cat b n (enc (open-req b d o nb n) kp)))
      (recv (hash (open-req b d o nb n)))))
  (defrole passer-close
    (vars (kp mesg) (n nb text) (d o b name) (del-key-locn locn))
    (trace (load del-key-locn (key-rec b d o nb n kp))
      (send (cat b n (enc (close-req b d o nb n) kp)))
      (recv (hash (close-req b d o nb n)))))
  (defrole dev-open
    (vars (k skey) (n nb text) (any mesg) (d o b name) (lk ls locn))
    (trace (load lk (dev-key-state d o k))
      (recv (cat b n (enc (open-req b d o nb n) (hash-dk b nb n k))))
      (load ls (door-state d any)) (load lk (dev-key-state d o k))
      (stor ls (door-state d (opened b nb n)))
      (send (hash (open-req b d o nb n))))
    (gen-st (dev-key-state d o k))
    (facts (same-dev ls lk)))
  (defrole dev-closed
    (vars (k skey) (n nb text) (any mesg) (d o b name) (lk ls locn))
    (trace (load lk (dev-key-state d o k))
      (recv (cat b n (enc (close-req b d o nb n) (hash-dk b nb n k))))
      (load ls (door-state d any)) (load lk (dev-key-state d o k))
      (stor ls (door-state d (closed o)))
      (send (hash (close-req b d o nb n))))
    (gen-st (dev-key-state d o k))
    (facts (same-dev ls lk)))
  (defrole dev-pass
    (vars (k skey) (n nb text) (d o b name) (lk ls locn))
    (trace (load lk (dev-key-state d o k))
      (load ls (door-state d (opened b nb n)))
      (recv (cat b nb n (enc "may I pass" (hash-dk b nb n k))))
      (send (enc "you may pass" n (hash-dk b nb n k))))
    (gen-st (dev-key-state d o k) (door-state d (opened b nb n)))
    (facts (same-dev ls lk)))
  (defrole passer-pass
    (vars (kp mesg) (n nb text) (d o b name) (del-key-locn locn))
    (trace (load del-key-locn (key-rec b d o nb n kp))
      (send (cat b nb n (enc "may I pass" kp)))
      (recv (enc "you may pass" kp))))
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
  (defgenrule fact-dev-closed-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-closed" z 3) (p "dev-closed" "lk" z lk)
          (p "dev-closed" "ls" z ls)) (fact same-dev ls lk))))
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
  (defgenrule trRl_passer-recv-key-at-4
    (forall ((z strd)) (implies (p "passer-recv-key" z 5) (trans z 4))))
  (defgenrule trRl_passer-recv-key-at-3
    (forall ((z strd)) (implies (p "passer-recv-key" z 5) (trans z 3))))
  (defgenrule trRl_dev-open-at-4
    (forall ((z strd)) (implies (p "dev-open" z 5) (trans z 4))))
  (defgenrule trRl_dev-open-at-2
    (forall ((z strd)) (implies (p "dev-open" z 5) (trans z 2))))
  (defgenrule trRl_dev-closed-at-4
    (forall ((z strd)) (implies (p "dev-closed" z 5) (trans z 4))))
  (defgenrule trRl_dev-closed-at-2
    (forall ((z strd)) (implies (p "dev-closed" z 5) (trans z 2))))
  (defgenrule eff-dev-up-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 4) (prec z 3 z1 i))
        (or (= z z1) (and (p "dev-up" z 5) (prec z 4 z1 i))))))
  (defgenrule cau-dev-up-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-open-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-open" z 4) (prec z1 i z 3))
        (or (= z z1) (prec z1 i z 2)))))
  (defgenrule cau-dev-closed-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-closed" z 4) (prec z1 i z 3))
        (or (= z z1) (prec z1 i z 2)))))
  (defgenrule cau-dev-pass-1
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-pass" z 2) (prec z1 i z 1))
        (or (= z z1) (prec z1 i z 0)))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-closed-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-closed" z 1) (p "dev-closed" "k" z k)
          (p "dev-closed" "o" z o) (p "dev-closed" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (n nb text) (b d name))
      (implies
        (and (p "dev-pass" z 2) (p "dev-pass" "n" z n)
          (p "dev-pass" "nb" z nb) (p "dev-pass" "b" z b)
          (p "dev-pass" "d" z d))
        (gen-st (door-state d (opened b nb n))))))
  (lang (closed (tuple 1)) (opened (tuple 3)) (door-state (tuple 2))
    (dev-key-state (tuple 3)) (open-req (tuple 5)) (close-req (tuple 5))
    (key-rec (tuple 6)) (delegate (tuple 6)) (hash-dk hash)))

(defskeleton open-closed
  (vars (k skey) (n nb text) (d o b name) (pt pt-0 pval) (lk ls locn))
  (defstrand dev-pass 4 (k k) (n n) (nb nb) (d d) (o o) (b b) (lk lk)
    (ls ls))
  (traces
    ((load lk (cat pt (dev-key-state d o k)))
      (load ls (cat pt-0 (door-state d (opened b nb n))))
      (recv (cat b nb n (enc "may I pass" (hash-dk b nb n k))))
      (send (enc "you may pass" n (hash-dk b nb n k)))))
  (label 3)
  (realized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton open-closed
  (vars (old old1 any mesg) (k skey) (n nb text) (b d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand dev-pass 4 (k k) (n n) (nb nb) (d d) (o o) (b b) (lk lk)
    (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand owner-power-dev 1 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-open 5 (any any) (k k) (n n) (nb nb) (d d) (o o) (b b)
    (lk lk) (ls ls))
  (precedes ((1 4) (3 0)) ((2 0) (1 0)) ((3 4) (0 0)))
  (gen-st (dev-key-state d o k) (door-state d (opened b nb n)))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 1 4) (trans 1 3) (trans 1 2)
    (trans 1 1) (trans 3 4) (trans 3 2))
  (operation channel-test (displaced 4 1 dev-up 4)
    (ch-msg lk (cat pt-5 (dev-key-state d o k))) (3 3))
  (traces
    ((load lk (cat pt-2 (dev-key-state d o k)))
      (load ls (cat pt (door-state d (opened b nb n))))
      (recv (cat b nb n (enc "may I pass" (hash-dk b nb n k))))
      (send (enc "you may pass" n (hash-dk b nb n k))))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1))
      (stor lk (cat pt-2 (dev-key-state d o k)))
      (stor ls (cat pt-3 (door-state d (closed o)))))
    ((send start-ch (cat "power-up" d o k)))
    ((load lk (cat pt-2 (dev-key-state d o k)))
      (recv (cat b n (enc (open-req b d o nb n) (hash-dk b nb n k))))
      (load ls (cat pt-4 (door-state d any)))
      (load lk (cat pt-2 (dev-key-state d o k)))
      (stor ls (cat pt (door-state d (opened b nb n))))))
  (label 10)
  (parent 3)
  (realized)
  (shape)
  (maps
    ((0)
      ((k k) (n n) (nb nb) (d d) (o o) (b b) (lk lk) (ls ls) (pt pt-2)
        (pt-0 pt))))
  (origs (pt-2 (1 3)) (pt-3 (1 4)) (pt (3 4))))

(comment "Nothing left to do")

(defprotocol open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan)
      (lk ls locn))
    (trace (recv start-ch (cat "power-up" d o k)) (load lk old)
      (load ls old1) (stor lk (dev-key-state d o k))
      (stor ls (door-state d (closed o))) (send (enc "up" k)))
    (auth start-ch)
    (facts (same-dev ls lk)))
  (defrole owner-power-dev
    (vars (k skey) (d o name) (start-ch chan))
    (trace (send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    (conf start-ch))
  (defrole owner-delg-key
    (vars (k skey) (n nb text) (d o b name) (to-b from-b chan))
    (trace (recv from-b (cat "req-key" b nb))
      (send to-b (delegate b d o nb n (hash-dk b nb n k)))
      (recv (hash b nb n)))
    (uniq-orig n)
    (conf to-b)
    (auth from-b))
  (defrole passer-recv-key
    (vars (kp ign mesg) (n nb text) (d o b name) (to-b from-b chan)
      (del-key-locn locn))
    (trace (send from-b (cat "req-key" b nb))
      (recv to-b (delegate b d o nb n kp)) (send (hash b nb n))
      (load del-key-locn ign)
      (stor del-key-locn (key-rec b d o nb n kp)))
    (uniq-orig nb)
    (auth to-b))
  (defrole passer-open
    (vars (kp mesg) (n nb text) (d o b name) (del-key-locn locn))
    (trace (load del-key-locn (key-rec b d o nb n kp))
      (send (cat b n (enc (open-req b d o nb n) kp)))
      (recv (hash (open-req b d o nb n)))))
  (defrole passer-close
    (vars (kp mesg) (n nb text) (d o b name) (del-key-locn locn))
    (trace (load del-key-locn (key-rec b d o nb n kp))
      (send (cat b n (enc (close-req b d o nb n) kp)))
      (recv (hash (close-req b d o nb n)))))
  (defrole dev-open
    (vars (k skey) (n nb text) (any mesg) (d o b name) (lk ls locn))
    (trace (load lk (dev-key-state d o k))
      (recv (cat b n (enc (open-req b d o nb n) (hash-dk b nb n k))))
      (load ls (door-state d any)) (load lk (dev-key-state d o k))
      (stor ls (door-state d (opened b nb n)))
      (send (hash (open-req b d o nb n))))
    (gen-st (dev-key-state d o k))
    (facts (same-dev ls lk)))
  (defrole dev-closed
    (vars (k skey) (n nb text) (any mesg) (d o b name) (lk ls locn))
    (trace (load lk (dev-key-state d o k))
      (recv (cat b n (enc (close-req b d o nb n) (hash-dk b nb n k))))
      (load ls (door-state d any)) (load lk (dev-key-state d o k))
      (stor ls (door-state d (closed o)))
      (send (hash (close-req b d o nb n))))
    (gen-st (dev-key-state d o k))
    (facts (same-dev ls lk)))
  (defrole dev-pass
    (vars (k skey) (n nb text) (d o b name) (lk ls locn))
    (trace (load lk (dev-key-state d o k))
      (load ls (door-state d (opened b nb n)))
      (recv (cat b nb n (enc "may I pass" (hash-dk b nb n k))))
      (send (enc "you may pass" n (hash-dk b nb n k))))
    (gen-st (dev-key-state d o k) (door-state d (opened b nb n)))
    (facts (same-dev ls lk)))
  (defrole passer-pass
    (vars (kp mesg) (n nb text) (d o b name) (del-key-locn locn))
    (trace (load del-key-locn (key-rec b d o nb n kp))
      (send (cat b nb n (enc "may I pass" kp)))
      (recv (enc "you may pass" kp))))
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
  (defgenrule fact-dev-closed-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-closed" z 3) (p "dev-closed" "lk" z lk)
          (p "dev-closed" "ls" z ls)) (fact same-dev ls lk))))
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
  (defgenrule trRl_passer-recv-key-at-4
    (forall ((z strd)) (implies (p "passer-recv-key" z 5) (trans z 4))))
  (defgenrule trRl_passer-recv-key-at-3
    (forall ((z strd)) (implies (p "passer-recv-key" z 5) (trans z 3))))
  (defgenrule trRl_dev-open-at-4
    (forall ((z strd)) (implies (p "dev-open" z 5) (trans z 4))))
  (defgenrule trRl_dev-open-at-2
    (forall ((z strd)) (implies (p "dev-open" z 5) (trans z 2))))
  (defgenrule trRl_dev-closed-at-4
    (forall ((z strd)) (implies (p "dev-closed" z 5) (trans z 4))))
  (defgenrule trRl_dev-closed-at-2
    (forall ((z strd)) (implies (p "dev-closed" z 5) (trans z 2))))
  (defgenrule eff-dev-up-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 4) (prec z 3 z1 i))
        (or (= z z1) (and (p "dev-up" z 5) (prec z 4 z1 i))))))
  (defgenrule cau-dev-up-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z 3) (prec z1 i z 2))
        (or (= z z1) (prec z1 i z 1)))))
  (defgenrule cau-dev-open-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-open" z 4) (prec z1 i z 3))
        (or (= z z1) (prec z1 i z 2)))))
  (defgenrule cau-dev-closed-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-closed" z 4) (prec z1 i z 3))
        (or (= z z1) (prec z1 i z 2)))))
  (defgenrule cau-dev-pass-1
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-pass" z 2) (prec z1 i z 1))
        (or (= z z1) (prec z1 i z 0)))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-open" z 1) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-closed-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-closed" z 1) (p "dev-closed" "k" z k)
          (p "dev-closed" "o" z o) (p "dev-closed" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-pass" z 1) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (n nb text) (b d name))
      (implies
        (and (p "dev-pass" z 2) (p "dev-pass" "n" z n)
          (p "dev-pass" "nb" z nb) (p "dev-pass" "b" z b)
          (p "dev-pass" "d" z d))
        (gen-st (door-state d (opened b nb n))))))
  (lang (closed (tuple 1)) (opened (tuple 3)) (door-state (tuple 2))
    (dev-key-state (tuple 3)) (open-req (tuple 5)) (close-req (tuple 5))
    (key-rec (tuple 6)) (delegate (tuple 6)) (hash-dk hash)))

(defskeleton open-closed
  (vars (k skey) (n nb text) (d o d-0 o-0 b name) (pt pt-0 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (nb nb) (d d-0) (o o-0) (b b)
    (lk lk) (ls ls))
  (uniq-orig k)
  (conf start-ch)
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt (dev-key-state d-0 o-0 k)))
      (load ls (cat pt-0 (door-state d-0 (opened b nb n))))
      (recv (cat b nb n (enc "may I pass" (hash-dk b nb n k))))
      (send (enc "you may pass" n (hash-dk b nb n k)))))
  (label 12)
  (unrealized (0 1) (1 0) (1 2))
  (preskeleton)
  (origs (k (0 0)))
  (comment "Not a skeleton"))

(defskeleton open-closed
  (vars (any ign old old1 mesg) (k skey) (n nb text) (b d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pval)
    (to-b from-b start-ch chan) (del-key-locn lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-pass 4 (k k) (n n) (nb nb) (d d) (o o) (b b) (lk lk)
    (ls ls))
  (defstrand dev-open 5 (any any) (k k) (n n) (nb nb) (d d) (o o) (b b)
    (lk lk) (ls ls))
  (defstrand passer-open 2 (kp (hash-dk b nb n k)) (n n) (nb nb) (d d)
    (o o) (b b) (del-key-locn del-key-locn))
  (defstrand owner-delg-key 2 (k k) (n n) (nb nb) (d d) (o o) (b b)
    (to-b to-b) (from-b from-b))
  (defstrand passer-recv-key 5 (kp (hash-dk b nb n k)) (ign ign) (n n)
    (nb nb) (d d) (o o) (b b) (to-b to-b) (from-b from-b)
    (del-key-locn del-key-locn))
  (defstrand passer-pass 2 (kp (hash-dk b nb n k)) (n n) (nb nb) (d d)
    (o o) (b b) (del-key-locn del-key-locn))
  (defstrand dev-up 6 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (precedes ((0 0) (7 0)) ((2 4) (1 0)) ((3 1) (2 1)) ((4 1) (5 1))
    ((5 0) (4 0)) ((5 4) (3 0)) ((5 4) (6 0)) ((6 1) (1 2))
    ((7 4) (2 0)) ((7 5) (0 1)))
  (uniq-orig k n nb)
  (gen-st (dev-key-state d o k) (door-state d (opened b nb n)))
  (conf to-b start-ch)
  (auth to-b from-b start-ch)
  (facts (same-dev ls lk) (trans 7 4) (trans 7 3) (trans 7 2)
    (trans 7 1) (trans 5 4) (trans 5 3) (trans 2 4) (trans 2 2))
  (operation encryption-test (displaced 2 8 dev-up 6) (enc "up" k)
    (0 1))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((load lk (cat pt-5 (dev-key-state d o k)))
      (load ls (cat pt (door-state d (opened b nb n))))
      (recv (cat b nb n (enc "may I pass" (hash-dk b nb n k))))
      (send (enc "you may pass" n (hash-dk b nb n k))))
    ((load lk (cat pt-5 (dev-key-state d o k)))
      (recv (cat b n (enc (open-req b d o nb n) (hash-dk b nb n k))))
      (load ls (cat pt-0 (door-state d any)))
      (load lk (cat pt-5 (dev-key-state d o k)))
      (stor ls (cat pt (door-state d (opened b nb n)))))
    ((load del-key-locn
       (cat pt-2 (key-rec b d o nb n (hash-dk b nb n k))))
      (send (cat b n (enc (open-req b d o nb n) (hash-dk b nb n k)))))
    ((recv from-b (cat "req-key" b nb))
      (send to-b (delegate b d o nb n (hash-dk b nb n k))))
    ((send from-b (cat "req-key" b nb))
      (recv to-b (delegate b d o nb n (hash-dk b nb n k)))
      (send (hash b nb n)) (load del-key-locn (cat pt-1 ign))
      (stor del-key-locn
        (cat pt-2 (key-rec b d o nb n (hash-dk b nb n k)))))
    ((load del-key-locn
       (cat pt-2 (key-rec b d o nb n (hash-dk b nb n k))))
      (send (cat b nb n (enc "may I pass" (hash-dk b nb n k)))))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-3 old))
      (load ls (cat pt-4 old1))
      (stor lk (cat pt-5 (dev-key-state d o k)))
      (stor ls (cat pt-6 (door-state d (closed o))))
      (send (enc "up" k))))
  (label 56)
  (parent 12)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((k k) (d d) (o o) (start-ch start-ch) (n n) (nb nb) (d-0 d)
        (o-0 o) (b b) (lk lk) (ls ls) (pt pt-5) (pt-0 pt))))
  (origs (pt-5 (7 3)) (pt-6 (7 4)) (nb (5 0)) (pt-2 (5 4)) (n (4 1))
    (pt (2 4)) (k (0 0))))

(comment "Nothing left to do")
