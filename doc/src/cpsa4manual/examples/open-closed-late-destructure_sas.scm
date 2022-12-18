(herald open-closed-late-destructure (bound 40))

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

(comment "All input read from open-closed-late-destructure.scm")

(comment "Strand count bounded at 40")

(defprotocol subatomic-open-closed basic
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
    (vars (k skey) (n nb text) (any request mesg) (d o b name)
      (lk ls locn))
    (trace (recv (cat b n nb request)) (load ls (door-state d any))
      (load lk (dev-key-state d o k))
      (stor ls (door-state d (opened b nb n)))
      (send (hash (open-req b d o nb n))))
    (gen-st (dev-key-state d o k))
    (facts (same-dev ls lk)))
  (defrole dev-closed
    (vars (k skey) (n nb text) (any request mesg) (d o b name)
      (lk ls locn))
    (trace (recv (cat b n nb request)) (load ls (door-state d any))
      (load lk (dev-key-state d o k))
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
  (defrule cheq-dev-open-4
    (forall ((z strd) (k skey) (n nb text) (o d b name) (request mesg))
      (implies
        (and (p "dev-open" z (idx 4)) (p "dev-open" "k" z k)
          (p "dev-open" "n" z n) (p "dev-open" "nb" z nb)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d)
          (p "dev-open" "b" z b) (p "dev-open" "request" z request))
        (= request (enc (open-req b d o nb n) (hash-dk b nb n k))))))
  (defrule cheq-dev-closed-4
    (forall ((z strd) (k skey) (n nb text) (o d b name) (request mesg))
      (implies
        (and (p "dev-closed" z (idx 4)) (p "dev-closed" "k" z k)
          (p "dev-closed" "n" z n) (p "dev-closed" "nb" z nb)
          (p "dev-closed" "o" z o) (p "dev-closed" "d" z d)
          (p "dev-closed" "b" z b) (p "dev-closed" "request" z request))
        (= request (enc (close-req b d o nb n) (hash-dk b nb n k))))))
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
        (and (p "dev-up" z (idx 3)) (p "dev-up" "lk" z lk)
          (p "dev-up" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-open-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-open" z (idx 3)) (p "dev-open" "lk" z lk)
          (p "dev-open" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-closed-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-closed" z (idx 3)) (p "dev-closed" "lk" z lk)
          (p "dev-closed" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-pass-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-pass" z (idx 2)) (p "dev-pass" "lk" z lk)
          (p "dev-pass" "ls" z ls)) (fact same-dev ls lk))))
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
  (defgenrule trRl_passer-recv-key-at-4
    (forall ((z strd))
      (implies (p "passer-recv-key" z (idx 5)) (trans z (idx 4)))))
  (defgenrule trRl_passer-recv-key-at-3
    (forall ((z strd))
      (implies (p "passer-recv-key" z (idx 5)) (trans z (idx 3)))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-open-at-1
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 1)))))
  (defgenrule trRl_dev-closed-at-3
    (forall ((z strd))
      (implies (p "dev-closed" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-closed-at-1
    (forall ((z strd))
      (implies (p "dev-closed" z (idx 4)) (trans z (idx 1)))))
  (defgenrule eff-dev-up-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z (idx 4)) (prec z (idx 3) z1 i))
        (or (= z z1)
          (and (p "dev-up" z (idx 5)) (prec z (idx 4) z1 i))))))
  (defgenrule cau-dev-up-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-open-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-open" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-closed-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-closed" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-pass-1
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-pass" z (idx 2)) (prec z1 i z (idx 1)))
        (or (= z z1) (prec z1 i z (idx 0))))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-open" z (idx 3)) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-closed-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-closed" z (idx 3)) (p "dev-closed" "k" z k)
          (p "dev-closed" "o" z o) (p "dev-closed" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (n nb text) (b d name))
      (implies
        (and (p "dev-pass" z (idx 2)) (p "dev-pass" "n" z n)
          (p "dev-pass" "nb" z nb) (p "dev-pass" "b" z b)
          (p "dev-pass" "d" z d))
        (gen-st (door-state d (opened b nb n))))))
  (lang (closed (tuple 1)) (opened (tuple 3)) (door-state (tuple 2))
    (dev-key-state (tuple 3)) (open-req (tuple 5)) (close-req (tuple 5))
    (key-rec (tuple 6)) (delegate (tuple 6)) (hash-dk hash)))

(defgoal subatomic-open-closed
  (forall ((k skey) (d o name) (start-ch chan) (z z-0 strd))
    (implies
      (and (p "owner-power-dev" z 2) (p "" z-0 2)
        (p "owner-power-dev" "k" z k) (p "owner-power-dev" "d" z d)
        (p "owner-power-dev" "o" z o)
        (p "owner-power-dev" "start-ch" z start-ch) (p "" "x" z-0 k)
        (uniq-at k z 0) (conf start-ch))
      (false))))

(defprotocol subatomic-open-closed basic
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
    (vars (k skey) (n nb text) (any request mesg) (d o b name)
      (lk ls locn))
    (trace (recv (cat b n nb request)) (load ls (door-state d any))
      (load lk (dev-key-state d o k))
      (stor ls (door-state d (opened b nb n)))
      (send (hash (open-req b d o nb n))))
    (gen-st (dev-key-state d o k))
    (facts (same-dev ls lk)))
  (defrole dev-closed
    (vars (k skey) (n nb text) (any request mesg) (d o b name)
      (lk ls locn))
    (trace (recv (cat b n nb request)) (load ls (door-state d any))
      (load lk (dev-key-state d o k))
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
  (defrule cheq-dev-open-4
    (forall ((z strd) (k skey) (n nb text) (o d b name) (request mesg))
      (implies
        (and (p "dev-open" z (idx 4)) (p "dev-open" "k" z k)
          (p "dev-open" "n" z n) (p "dev-open" "nb" z nb)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d)
          (p "dev-open" "b" z b) (p "dev-open" "request" z request))
        (= request (enc (open-req b d o nb n) (hash-dk b nb n k))))))
  (defrule cheq-dev-closed-4
    (forall ((z strd) (k skey) (n nb text) (o d b name) (request mesg))
      (implies
        (and (p "dev-closed" z (idx 4)) (p "dev-closed" "k" z k)
          (p "dev-closed" "n" z n) (p "dev-closed" "nb" z nb)
          (p "dev-closed" "o" z o) (p "dev-closed" "d" z d)
          (p "dev-closed" "b" z b) (p "dev-closed" "request" z request))
        (= request (enc (close-req b d o nb n) (hash-dk b nb n k))))))
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
        (and (p "dev-up" z (idx 3)) (p "dev-up" "lk" z lk)
          (p "dev-up" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-open-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-open" z (idx 3)) (p "dev-open" "lk" z lk)
          (p "dev-open" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-closed-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-closed" z (idx 3)) (p "dev-closed" "lk" z lk)
          (p "dev-closed" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-pass-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-pass" z (idx 2)) (p "dev-pass" "lk" z lk)
          (p "dev-pass" "ls" z ls)) (fact same-dev ls lk))))
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
  (defgenrule trRl_passer-recv-key-at-4
    (forall ((z strd))
      (implies (p "passer-recv-key" z (idx 5)) (trans z (idx 4)))))
  (defgenrule trRl_passer-recv-key-at-3
    (forall ((z strd))
      (implies (p "passer-recv-key" z (idx 5)) (trans z (idx 3)))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-open-at-1
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 1)))))
  (defgenrule trRl_dev-closed-at-3
    (forall ((z strd))
      (implies (p "dev-closed" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-closed-at-1
    (forall ((z strd))
      (implies (p "dev-closed" z (idx 4)) (trans z (idx 1)))))
  (defgenrule eff-dev-up-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z (idx 4)) (prec z (idx 3) z1 i))
        (or (= z z1)
          (and (p "dev-up" z (idx 5)) (prec z (idx 4) z1 i))))))
  (defgenrule cau-dev-up-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-open-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-open" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-closed-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-closed" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-pass-1
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-pass" z (idx 2)) (prec z1 i z (idx 1)))
        (or (= z z1) (prec z1 i z (idx 0))))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-open" z (idx 3)) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-closed-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-closed" z (idx 3)) (p "dev-closed" "k" z k)
          (p "dev-closed" "o" z o) (p "dev-closed" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (n nb text) (b d name))
      (implies
        (and (p "dev-pass" z (idx 2)) (p "dev-pass" "n" z n)
          (p "dev-pass" "nb" z nb) (p "dev-pass" "b" z b)
          (p "dev-pass" "d" z d))
        (gen-st (door-state d (opened b nb n))))))
  (lang (closed (tuple 1)) (opened (tuple 3)) (door-state (tuple 2))
    (dev-key-state (tuple 3)) (open-req (tuple 5)) (close-req (tuple 5))
    (key-rec (tuple 6)) (delegate (tuple 6)) (hash-dk hash)))

(defgoal subatomic-open-closed
  (forall ((k skey) (n nb text) (d o b name) (lk ls locn) (z strd))
    (implies
      (and (p "dev-pass" z 4) (p "dev-pass" "k" z k)
        (p "dev-pass" "n" z n) (p "dev-pass" "nb" z nb)
        (p "dev-pass" "d" z d) (p "dev-pass" "o" z o)
        (p "dev-pass" "b" z b) (p "dev-pass" "lk" z lk)
        (p "dev-pass" "ls" z ls))
      (exists ((old old1 any mesg) (start-ch chan) (z-0 z-1 z-2 strd))
        (and (p "dev-up" z-0 5) (p "owner-power-dev" z-1 1)
          (p "dev-open" z-2 4) (p "dev-up" "old" z-0 old)
          (p "dev-up" "old1" z-0 old1) (p "dev-up" "k" z-0 k)
          (p "dev-up" "d" z-0 d) (p "dev-up" "o" z-0 o)
          (p "dev-up" "start-ch" z-0 start-ch) (p "dev-up" "lk" z-0 lk)
          (p "dev-up" "ls" z-0 ls) (p "owner-power-dev" "k" z-1 k)
          (p "owner-power-dev" "d" z-1 d)
          (p "owner-power-dev" "o" z-1 o)
          (p "owner-power-dev" "start-ch" z-1 start-ch)
          (p "dev-open" "any" z-2 any)
          (p "dev-open" "request" z-2
            (enc (open-req b d o nb n) (hash-dk b nb n k)))
          (p "dev-open" "k" z-2 k) (p "dev-open" "n" z-2 n)
          (p "dev-open" "nb" z-2 nb) (p "dev-open" "d" z-2 d)
          (p "dev-open" "o" z-2 o) (p "dev-open" "b" z-2 b)
          (p "dev-open" "lk" z-2 lk) (p "dev-open" "ls" z-2 ls)
          (prec z-0 4 z-2 1) (prec z-1 0 z-0 0) (prec z-2 3 z 0)
          (gen-st (dev-key-state d o k))
          (gen-st (door-state d (opened b nb n))) (leads-to z-0 3 z 0)
          (leads-to z-0 3 z-2 2) (leads-to z-2 3 z 1) (auth start-ch)
          (conf start-ch) (fact same-dev ls lk))))))

(defprotocol subatomic-open-closed basic
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
    (vars (k skey) (n nb text) (any request mesg) (d o b name)
      (lk ls locn))
    (trace (recv (cat b n nb request)) (load ls (door-state d any))
      (load lk (dev-key-state d o k))
      (stor ls (door-state d (opened b nb n)))
      (send (hash (open-req b d o nb n))))
    (gen-st (dev-key-state d o k))
    (facts (same-dev ls lk)))
  (defrole dev-closed
    (vars (k skey) (n nb text) (any request mesg) (d o b name)
      (lk ls locn))
    (trace (recv (cat b n nb request)) (load ls (door-state d any))
      (load lk (dev-key-state d o k))
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
  (defrule cheq-dev-open-4
    (forall ((z strd) (k skey) (n nb text) (o d b name) (request mesg))
      (implies
        (and (p "dev-open" z (idx 4)) (p "dev-open" "k" z k)
          (p "dev-open" "n" z n) (p "dev-open" "nb" z nb)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d)
          (p "dev-open" "b" z b) (p "dev-open" "request" z request))
        (= request (enc (open-req b d o nb n) (hash-dk b nb n k))))))
  (defrule cheq-dev-closed-4
    (forall ((z strd) (k skey) (n nb text) (o d b name) (request mesg))
      (implies
        (and (p "dev-closed" z (idx 4)) (p "dev-closed" "k" z k)
          (p "dev-closed" "n" z n) (p "dev-closed" "nb" z nb)
          (p "dev-closed" "o" z o) (p "dev-closed" "d" z d)
          (p "dev-closed" "b" z b) (p "dev-closed" "request" z request))
        (= request (enc (close-req b d o nb n) (hash-dk b nb n k))))))
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
        (and (p "dev-up" z (idx 3)) (p "dev-up" "lk" z lk)
          (p "dev-up" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-open-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-open" z (idx 3)) (p "dev-open" "lk" z lk)
          (p "dev-open" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-closed-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-closed" z (idx 3)) (p "dev-closed" "lk" z lk)
          (p "dev-closed" "ls" z ls)) (fact same-dev ls lk))))
  (defgenrule fact-dev-pass-same-dev0
    (forall ((z strd) (lk ls locn))
      (implies
        (and (p "dev-pass" z (idx 2)) (p "dev-pass" "lk" z lk)
          (p "dev-pass" "ls" z ls)) (fact same-dev ls lk))))
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
  (defgenrule trRl_passer-recv-key-at-4
    (forall ((z strd))
      (implies (p "passer-recv-key" z (idx 5)) (trans z (idx 4)))))
  (defgenrule trRl_passer-recv-key-at-3
    (forall ((z strd))
      (implies (p "passer-recv-key" z (idx 5)) (trans z (idx 3)))))
  (defgenrule trRl_dev-open-at-3
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-open-at-1
    (forall ((z strd))
      (implies (p "dev-open" z (idx 4)) (trans z (idx 1)))))
  (defgenrule trRl_dev-closed-at-3
    (forall ((z strd))
      (implies (p "dev-closed" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_dev-closed-at-1
    (forall ((z strd))
      (implies (p "dev-closed" z (idx 4)) (trans z (idx 1)))))
  (defgenrule eff-dev-up-3
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z (idx 4)) (prec z (idx 3) z1 i))
        (or (= z z1)
          (and (p "dev-up" z (idx 5)) (prec z (idx 4) z1 i))))))
  (defgenrule cau-dev-up-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-up" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-open-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-open" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-closed-2
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-closed" z (idx 3)) (prec z1 i z (idx 2)))
        (or (= z z1) (prec z1 i z (idx 1))))))
  (defgenrule cau-dev-pass-1
    (forall ((z z1 strd) (i indx))
      (implies (and (p "dev-pass" z (idx 2)) (prec z1 i z (idx 1)))
        (or (= z z1) (prec z1 i z (idx 0))))))
  (defgenrule gen-st-dev-open-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-open" z (idx 3)) (p "dev-open" "k" z k)
          (p "dev-open" "o" z o) (p "dev-open" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-closed-0
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-closed" z (idx 3)) (p "dev-closed" "k" z k)
          (p "dev-closed" "o" z o) (p "dev-closed" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-pass-1
    (forall ((z strd) (k skey) (o d name))
      (implies
        (and (p "dev-pass" z (idx 1)) (p "dev-pass" "k" z k)
          (p "dev-pass" "o" z o) (p "dev-pass" "d" z d))
        (gen-st (dev-key-state d o k)))))
  (defgenrule gen-st-dev-pass-0
    (forall ((z strd) (n nb text) (b d name))
      (implies
        (and (p "dev-pass" z (idx 2)) (p "dev-pass" "n" z n)
          (p "dev-pass" "nb" z nb) (p "dev-pass" "b" z b)
          (p "dev-pass" "d" z d))
        (gen-st (door-state d (opened b nb n))))))
  (lang (closed (tuple 1)) (opened (tuple 3)) (door-state (tuple 2))
    (dev-key-state (tuple 3)) (open-req (tuple 5)) (close-req (tuple 5))
    (key-rec (tuple 6)) (delegate (tuple 6)) (hash-dk hash)))

(defgoal subatomic-open-closed
  (forall
    ((k skey) (n nb text) (d o d-0 o-0 b name) (start-ch chan)
      (lk ls locn) (z z-0 strd))
    (implies
      (and (p "owner-power-dev" z 2) (p "dev-pass" z-0 4)
        (p "owner-power-dev" "k" z k) (p "owner-power-dev" "d" z d)
        (p "owner-power-dev" "o" z o)
        (p "owner-power-dev" "start-ch" z start-ch)
        (p "dev-pass" "k" z-0 k) (p "dev-pass" "n" z-0 n)
        (p "dev-pass" "nb" z-0 nb) (p "dev-pass" "d" z-0 d-0)
        (p "dev-pass" "o" z-0 o-0) (p "dev-pass" "b" z-0 b)
        (p "dev-pass" "lk" z-0 lk) (p "dev-pass" "ls" z-0 ls)
        (uniq-at k z 0) (conf start-ch))
      (exists
        ((any ign old old1 mesg) (to-b from-b chan) (del-key-locn locn)
          (z-1 z-2 z-3 z-4 z-5 z-6 strd))
        (and (= d-0 d) (= o-0 o) (p "dev-open" z-1 4)
          (p "passer-open" z-2 2) (p "owner-delg-key" z-3 2)
          (p "passer-recv-key" z-4 5) (p "passer-pass" z-5 2)
          (p "dev-up" z-6 6) (p "dev-pass" "d" z-0 d)
          (p "dev-pass" "o" z-0 o) (p "dev-open" "any" z-1 any)
          (p "dev-open" "request" z-1
            (enc (open-req b d o nb n) (hash-dk b nb n k)))
          (p "dev-open" "k" z-1 k) (p "dev-open" "n" z-1 n)
          (p "dev-open" "nb" z-1 nb) (p "dev-open" "d" z-1 d)
          (p "dev-open" "o" z-1 o) (p "dev-open" "b" z-1 b)
          (p "dev-open" "lk" z-1 lk) (p "dev-open" "ls" z-1 ls)
          (p "passer-open" "kp" z-2 (hash-dk b nb n k))
          (p "passer-open" "n" z-2 n) (p "passer-open" "nb" z-2 nb)
          (p "passer-open" "d" z-2 d) (p "passer-open" "o" z-2 o)
          (p "passer-open" "b" z-2 b)
          (p "passer-open" "del-key-locn" z-2 del-key-locn)
          (p "owner-delg-key" "k" z-3 k) (p "owner-delg-key" "n" z-3 n)
          (p "owner-delg-key" "nb" z-3 nb)
          (p "owner-delg-key" "d" z-3 d) (p "owner-delg-key" "o" z-3 o)
          (p "owner-delg-key" "b" z-3 b)
          (p "owner-delg-key" "to-b" z-3 to-b)
          (p "owner-delg-key" "from-b" z-3 from-b)
          (p "passer-recv-key" "kp" z-4 (hash-dk b nb n k))
          (p "passer-recv-key" "ign" z-4 ign)
          (p "passer-recv-key" "n" z-4 n)
          (p "passer-recv-key" "nb" z-4 nb)
          (p "passer-recv-key" "d" z-4 d)
          (p "passer-recv-key" "o" z-4 o)
          (p "passer-recv-key" "b" z-4 b)
          (p "passer-recv-key" "to-b" z-4 to-b)
          (p "passer-recv-key" "from-b" z-4 from-b)
          (p "passer-recv-key" "del-key-locn" z-4 del-key-locn)
          (p "passer-pass" "kp" z-5 (hash-dk b nb n k))
          (p "passer-pass" "n" z-5 n) (p "passer-pass" "nb" z-5 nb)
          (p "passer-pass" "d" z-5 d) (p "passer-pass" "o" z-5 o)
          (p "passer-pass" "b" z-5 b)
          (p "passer-pass" "del-key-locn" z-5 del-key-locn)
          (p "dev-up" "old" z-6 old) (p "dev-up" "old1" z-6 old1)
          (p "dev-up" "k" z-6 k) (p "dev-up" "d" z-6 d)
          (p "dev-up" "o" z-6 o) (p "dev-up" "start-ch" z-6 start-ch)
          (p "dev-up" "lk" z-6 lk) (p "dev-up" "ls" z-6 ls)
          (prec z 0 z-6 0) (prec z-1 3 z-0 0) (prec z-2 1 z-1 0)
          (prec z-3 1 z-4 1) (prec z-4 0 z-3 0) (prec z-4 4 z-2 0)
          (prec z-4 4 z-5 0) (prec z-5 1 z-0 2) (prec z-6 4 z-1 1)
          (prec z-6 5 z 1) (uniq-at nb z-4 0) (uniq-at n z-3 1)
          (gen-st (dev-key-state d o k))
          (gen-st (door-state d (opened b nb n))) (leads-to z-1 3 z-0 1)
          (leads-to z-4 4 z-2 0) (leads-to z-4 4 z-5 0)
          (leads-to z-6 3 z-0 0) (leads-to z-6 3 z-1 2) (auth to-b)
          (auth from-b) (auth start-ch) (conf to-b)
          (fact same-dev ls lk))))))
