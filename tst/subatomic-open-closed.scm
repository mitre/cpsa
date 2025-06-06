(herald subatomic-open-closed
	;; (try-old-strands)
	;; 	(check-nonces)
	;; 	(reverse-nodes)
	(bound 40))

(defmacro (dev-key-state d o k)
  (cat "st-k" d o k))

(defmacro (opened o)
  (cat o o))

(defmacro (closed o) o)

(defmacro (dev-state-opened d o)
  (cat "st" d (opened o)))

(defmacro (dev-state-closed d o)
  (cat "st" d (closed o)))

(defmacro (dev-state-any d o any)
  (cat "st" d any))

(defprotocol subatomic-open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan) (lk ls locn))
    (trace
     (recv start-ch (cat "power-up" d o k))
     (load lk old)
     (load ls old1)
     (stor lk (dev-key-state d o k))
     (stor ls (dev-state-closed d o))
     (send (enc "up" k)))
    (auth start-ch)
    ;; Critical section declarations are now obsolete.  
    ;; (critical-sections (1 4))
    (facts (same-dev ls lk)))

  (defrole owner-power-dev
    (vars (k skey) (d o name) (start-ch chan))
    (trace
     (send start-ch (cat "power-up" d o k))
     (recv (enc "up" k)))
    (conf start-ch))

  (defrole owner-open
    (vars (k skey) (n text) (d o name))
    (trace
     (send (enc "open" d o n k))
     (recv n)))

  (defrole owner-close
    (vars (k skey) (n text) (d o name))
    (trace
     (send (enc "close" d o n k))
     (recv n)))

  (defrole dev-open
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace
     (recv (enc "open" d o n k))
     (load ls (dev-state-any d o any))
     (load lk (dev-key-state d o k))
     (stor ls (dev-state-opened d o))
     (send n))
    ;; Critical section declarations are now obsolete.  
    ;; (critical-sections (1 3))
    (gen-st (dev-key-state d o k) (dev-state-opened d o))
    (facts (same-dev ls lk)))

  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace
     (recv (enc "close" d o n k))
     (load lk (dev-key-state d o k))
     (load ls (dev-state-any d o any))
     (stor ls (dev-state-closed d o))
     (send n))
    (gen-st (dev-key-state d o k))
    ;; Critical section declarations are now obsolete.  
    ;; (critical-sections (1 3))
    (facts (same-dev ls lk)))

  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace
     (load lk (dev-key-state d o k))
     (load ls (dev-state-opened d o))
     (recv (enc "may I pass" k))
     (send (enc "you may pass" n k)))
    (uniq-orig n)
    (gen-st (dev-key-state d o k) (dev-state-opened d o))
    ;; Critical section declarations are now obsolete.  
    ;; (critical-sections (0 1))
    (facts (same-dev ls lk)))

  (defrole user-pass
    (vars (k skey) (n text) (d o name) (l locn))
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

   (defrule same-dev-ls-lk
     (forall ((ls lk lk-0 locn))
  	     (implies
  	      (and (fact same-dev ls lk)
  		   (fact same-dev ls lk-0))
  	      (= lk lk-0))))

   (defrule same-dev-lk-ls
     (forall ((lk ls ls-0 locn))
  	     (implies
  	      (and (fact same-dev ls lk)
  		   (fact same-dev ls-0 lk))
     	      (= ls ls-0)))))

(defskeleton subatomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand owner-power-dev 2 (k k))
  (deflistener k)
  (uniq-orig k)
  (facts (no-state-split)))

(defskeleton subatomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand dev-pass 4 (k k))
  (facts (no-state-split)))

(defskeleton subatomic-open-closed
	   (vars (k skey) (d o name) (n text) (start-ch chan))
	   (defstrand owner-power-dev 2 (k k))
	   (defstrand dev-pass 4 (k k))
	   (uniq-orig k)
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
