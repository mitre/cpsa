(herald open-closed 
	;; (try-old-strands) 
	;; 	(check-nonces)
	;; 	(reverse-nodes) 
	(bound 44))

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

(defprotocol open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan) (lk ls locn))
    (trace
     (recv start-ch (cat "power-up" d o k))
     (load lk old) 
     (stor lk (dev-key-state d o k))
     (load ls old1)
     (stor ls (dev-state-closed d o))
     (send (enc "up" k)))
    (auth start-ch))

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
     (load lk (dev-key-state d o k))
     (recv (enc "open" d o n k))
     (load ls (dev-state-any d o any)) 
     (stor ls (dev-state-opened d o))
     (send n)))

  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace
     (load lk (dev-key-state d o k))
     (recv (enc "close" d o n k))
     (load ls (dev-state-any d o any))
     (stor ls (dev-state-closed d o))
     (send n)))

  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace
     (load lk (dev-key-state d o k))
     (recv (enc "may I pass" k))
     (load ls (dev-state-opened d o))
     (send (enc "you may pass" n k)))
    (uniq-orig n))

  (defrole user-pass
    (vars (k skey) (n text) (d o name) (l locn))
    (trace
     (send (enc "may I pass" k))
     (recv (enc "you may pass" k))))

  (defrule gen-state-close 
    (forall ((z strd) (d o name) (k skey))
	    (implies
	     (and (p "dev-close" z 1)
		  (p "dev-close" "d" z d)
		  (p "dev-close" "o" z o)
		  (p "dev-close" "k" z k)
		  (p "dev-close" "any" z (opened o)))
	     (gen-st (dev-state-opened d o)))))
	     
  (defrule gen-state-pass 
    (forall ((z strd) (d o name) (k skey))
	    (implies
	     (and (p "dev-pass" z 1)
		  (p "dev-pass" "d" z d) 
		  (p "dev-pass" "o" z o)
		  (p "dev-pass" "k" z k))
	     (gen-st (dev-state-opened d o)))))

   (defrule power-deliver-once
     (forall
      ((z1 z2 strd) (k skey))
      (implies
       (and (p "dev-up" z1 2)
 	   (p "dev-up" z2 2)
 	   (p "dev-up" "k" z1 k)
 	   (p "dev-up" "k" z2 k))
       (= z1 z2))))
  )

(defskeleton open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand owner-power-dev 2 (k k))
  (deflistener k)
  (uniq-orig k))

(defskeleton open-closed 
  (vars (k skey) (d o name) (n text) (start-ch chan))
  ;; (defstrand owner-power-dev 2 (k k))
  (defstrand dev-pass 4 (k k))
  ;; (uniq-orig k)
  ) 

(defskeleton open-closed 
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand owner-power-dev 2 (k k))
  (defstrand dev-pass 4 (k k))
  (uniq-orig k))


(comment
 (defskeleton open-closed
   (vars (any old old1 mesg) (n n-0 text) (d o name) (k k-0 skey)
	 (start-ch chan) (ls lk lk-0 ls-0 locn))
   (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
   (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk ;-0
						     ) (ls ls))
   (defstrand user-pass 1 (k k))
   (defstrand dev-open 4 (any any) (n n-0) (d d) (o o) (k k-0) (lk lk)
     (ls ls))
   (defstrand dev-up 6 (old old) (old1 old1) (d d) (o o) (k k)
     (start-ch start-ch) (lk lk-0) (ls ls-0))
   (precedes ((0 0) (4 0)) ((2 0) (1 1)) ((3 3) (1 2)) ((4 2) (1 0))
	     ((4 5) (0 1)))
   (uniq-orig n k))

 (defskeleton open-closed
   (vars (any old old1 mesg) (n n-0 text) (d o name) (k k-0 skey)
	 (start-ch chan) (ls lk ls-0 locn))
   (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
   (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk) (ls ls))
   (defstrand user-pass 1 (k k))
   (defstrand dev-open 4 (any any) (n n-0) (d d) (o o) (k k-0) (lk lk)
     (ls ls))
   (defstrand dev-up 6 (old old) (old1 old1) (d d) (o o) (k k)
     (start-ch start-ch) (lk lk) (ls ls	; -0
				     )) 
   (precedes ((0 0) (4 0)) ((2 0) (1 1)) ((3 3) (1 2)) ((4 2) (1 0))
	     ((4 5) (0 1)))
   (uniq-orig n k)))

