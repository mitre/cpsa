(herald
 dev-subatomic-open-closed
 (comment "Version that uses (dev const) pairs for locations"))

(defmacro (dev-key-state o k)
  (cat "st-k" o k))

(defmacro (opened o)
  (cat o o))

(defmacro (closed o) o)

(defmacro (dev-state-opened o)
  (cat "st" (opened o)))

(defmacro (dev-state-closed o)
  (cat "st" (closed o)))

(defmacro (dev-state-any o any)
  (cat "st" any))

(defprotocol subatomic-open-closed basic
  (defrole dev-up
    (vars (k skey) (d dev) (o name) (old old1 mesg) (start-ch chan))
    (trace
     (recv start-ch (cat "power-up" o k))
     (stor (cat d "lk") (dev-key-state o k))
     (stor (cat d "ls") (dev-state-closed o))
     (send (enc "up" k)))
    (auth start-ch)
    )

  (defrole owner-power-dev
    (vars (k skey) (o name) (start-ch chan))
    (trace
     (send start-ch (cat "power-up" o k))
     (recv (enc "up" k)))
    (conf start-ch))

  (defrole owner-open
    (vars (k skey) (n text) (d dev) (o name))
    (trace
     (send (enc "open" d o n k))
     (recv n)))

  (defrole owner-close
    (vars (k skey) (n text) (d dev) (o name))
    (trace
     (send (enc "close" d o n k))
     (recv n)))

  (defrole dev-open
    (vars (k skey) (n text) (any mesg) (d dev) (o name))
    (trace
     (recv (enc "open" d o n k))
     (load (cat d "lk") (dev-key-state o k))
     (stor (cat d "ls") (dev-state-opened o))
     (send n))
    (gen-st (dev-key-state o k) (dev-state-opened o))
    )

  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d dev) (o name))
    (trace
     (recv (enc "close" d o n k))
     (load (cat d "lk") (dev-key-state o k))
     (stor (cat d "ls") (dev-state-closed o))
     (send n))
    (gen-st (dev-key-state o k))
    )

  (defrole dev-pass
    (vars (k skey) (n text) (d dev) (o name))
    (trace
     (load (cat d "lk") (dev-key-state o k))
     (load (cat d "ls") (dev-state-opened o))
     (recv (enc "may I pass" k))
     (send (enc "you may pass" n k)))
    (uniq-orig n)
    (gen-st (dev-key-state o k) (dev-state-opened o))
    )

  (defrole user-pass
    (vars (k skey))
    (trace
     (send (enc "may I pass" k))
     (recv (enc "you may pass" k))))

   (defrule power-deliver-once
     (forall
      ((z1 z2 strd) (k skey))
      (implies
       (and (p "dev-up" z1 2)
 	   (p "dev-up" z2 2)
 	   (p "dev-up" "k" z1 k)
 	   (p "dev-up" "k" z2 k))
       (= z1 z2))))

   ;; (defrule locName
   ;;   (forall
   ;;    ((l1 l2 locn) (m mesg))
   ;;    (implies
   ;;     (and (fact useLocName)
   ;; 	    (fact locName l1 m)
   ;; 	    (fact locName l2 m))
   ;;     (= l1 l2))))
)

(defskeleton subatomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand owner-power-dev 2 (k k))
  (deflistener k)
  (uniq-orig k)
  (facts (no-state-split)))

(defskeleton subatomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand dev-pass 4 (k k))
  (facts (no-state-split) (useLocName)))

(defskeleton subatomic-open-closed
	   (vars (k skey) (d o name) (n text) (start-ch chan))
	   (defstrand owner-power-dev 2 (k k))
	   (defstrand dev-pass 4 (k k))
	   (uniq-orig k)
	   (facts (no-state-split)))

;; When the locName rule is disabled CPSA considers it
;; possible that a given device may have several key-state
;; locations and several door-state locations. These wires
;; can get crossed. The locName fact and rule allow us to
;; treat ls and lk as fixed constant addresses on each
;; device d. 
(defskeleton subatomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand dev-pass 4 (k k))
  (facts (no-state-split)))

(comment
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
   ;;  (facts (same-dev ls lk) (no-state-split))
   (leads-to ((2 3) (1 1)) ((5 3) (1 0)) ((5 3) (2 2)))))
