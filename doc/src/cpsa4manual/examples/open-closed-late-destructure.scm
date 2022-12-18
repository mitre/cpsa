(herald open-closed-late-destructure
	(bound 40))

(defprotocol subatomic-open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan) (lk ls locn))
    (trace
     (recv start-ch (cat "power-up" d o k))
     (load lk old)
     (load ls old1)
     (stor lk (dev-key-state d o k))
     (stor ls (door-state d (closed o)))
     (send (enc "up" k)))
    (auth start-ch)
    ;; (critical-sections (1 4))
    (facts (same-dev ls lk)))

  (defrole owner-power-dev
    (vars (k skey) (d o name) (start-ch chan))
    (trace
     (send start-ch (cat "power-up" d o k))
     (recv (enc "up" k)))
    (conf start-ch))

  (defrole owner-delg-key
    (vars (k skey) (n nb text) (d o b name) (to-b from-b chan))
    (trace
     (recv from-b (cat "req-key" b nb))
     (send to-b (delegate b d o nb n (hash-dk (cat b nb n k))))
     (recv (hash b nb n)))
     (conf to-b)
     (auth from-b)
    (uniq-orig n))

  (defrole passer-recv-key
    (vars (kp ign mesg) (n nb text) (d o b name) (to-b from-b chan) (del-key-locn locn))
    (trace
     (send from-b (cat "req-key" b nb))
     (recv to-b (delegate b d o nb n kp))
     (send (hash b nb n))
     (load del-key-locn ign)
     (stor del-key-locn (key-rec b d o nb n kp)))
    (uniq-orig nb)
    (auth to-b))

  (defrole passer-open
    (vars (kp ign mesg) (n nb text) (d o b name) (to-b chan) (del-key-locn locn))
    (trace
     (load del-key-locn (key-rec b d o nb n kp))
     (send (cat b n (enc (open-req b d o nb n) kp)))
     (recv (hash (open-req b d o nb n)))))

  (defrole passer-close
    (vars (kp ign mesg) (n nb text) (d o b name) (to-b chan) (del-key-locn locn))
    (trace
     (load del-key-locn (key-rec b d o nb n kp))
     (send (cat b n (enc (close-req b d o nb n) kp)))
     (recv (hash (close-req b d o nb n)))))

  (defrole dev-open
    (vars (k skey) (n nb text) (any new-key-state request mesg) (d o b name) (lk ls locn))
    (trace
     (recv (cat b n nb request))
     (load ls (door-state d any))
     (load lk (dev-key-state d o k))
     (cheq request (enc (open-req b d o nb n)
			(hash-dk (cat b nb n k))))
     (stor ls (door-state d (opened b nb n)))
     (send (hash (open-req b d o nb n))))
    (gen-st (dev-key-state d o k))
    (facts (same-dev ls lk)))

  (defrole dev-closed
    (vars (k skey) (n nb text) (any new-key-state request mesg) (d o b name) (lk ls locn))
    (trace
     (recv (cat b n nb request))
     (load ls (door-state d any))
     (load lk (dev-key-state d o k))
     (cheq request (enc (close-req b d o nb n)
			(hash-dk (cat b nb n k))))
     (stor ls (door-state d (closed o)))
     (send (hash (close-req b d o nb n))))
    (gen-st (dev-key-state d o k))
    (facts (same-dev ls lk)))

  (defrole dev-pass
    (vars (k skey) (n nb text) (d o b name) (lk ls locn))
    (trace
     (load lk (dev-key-state d o k))
     (load ls (door-state d (opened b nb n)))
     (recv (cat b nb n (enc "may I pass" (hash-dk (cat b nb n k)))))
     (send (enc "you may pass" n (hash-dk (cat b nb n k)))))
    (gen-st (dev-key-state d o k) (door-state d (opened b nb n)))
    ;;    (critical-sections (0 1))
    (facts (same-dev ls lk)))

  (defrole passer-pass
    (vars (kp ign mesg) (n nb text) (d o b name) (to-b chan) (del-key-locn locn))
    (trace
     (load del-key-locn (key-rec b d o nb n kp))
     (send (cat b nb n (enc "may I pass" kp)))
     (recv (enc "you may pass" kp))))

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
     	      (= ls ls-0))))

   (lang (closed (tuple 1))
	 (opened (tuple 3))
	 (door-state (tuple 2))
	 (dev-key-state (tuple 3))
	 (open-req (tuple 5))
	 (close-req (tuple 5))
	 (key-rec (tuple 6))
	 (delegate (tuple 6))
	 (hash-dk hash)))

(defskeleton subatomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand owner-power-dev 2 (k k))
  (deflistener k)
  (uniq-orig k))

(defskeleton subatomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand dev-pass 4 (k k)))

(defskeleton subatomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand owner-power-dev 2 (k k))
  (defstrand dev-pass 4 (k k))
  (uniq-orig k))

(comment
 (defskeleton subatomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand dev-pass 4 (k k) (d d) (o o))
  (gen-st (dev-key-state d o k)))

 )
