(herald atomic-open-closed
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

(defprotocol atomic-open-closed basic
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
     (recv (enc "open" d o n k))
     (load lk (dev-key-state d o k))
     (load ls (dev-state-any d o any))
     (stor ls (dev-state-opened d o))
     (send n)))

  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace
     (recv (enc "close" d o n k))
     (load lk (dev-key-state d o k))
     (load ls (dev-state-any d o any))
     (stor ls (dev-state-closed d o))
     (send n)))

  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace
     (recv (enc "may I pass" k))
     (load lk (dev-key-state d o k))
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

  (defrule gen-state-open
    (forall ((z strd) (d o k mesg))
	    (implies
	     (and (p "dev-open" "d" z d)
		  (p "dev-open" "o" z o)
		  (p "dev-open" "k" z k))
	     (gen-st (dev-key-state d o k)))))

  (defrule gen-state-close
    (forall ((z strd) (d o k mesg))
	    (implies
	     (and (p "dev-close" "d" z d)
		  (p "dev-close" "o" z o)
		  (p "dev-close" "k" z k))
	     (gen-st (dev-key-state d o k)))))

  (defrule gen-state-pass
    (forall ((z strd) (d o k mesg))
	    (implies
	     (and (p "dev-pass" "d" z d)
		  (p "dev-pass" "o" z o)
		  (p "dev-pass" "k" z k))
	     (and (gen-st (dev-key-state d o k))))))

   (defrule power-deliver-once
     (forall
      ((z1 z2 strd) (k skey))
      (implies
       (and (p "dev-up" z1 2)
 	   (p "dev-up" z2 2)
 	   (p "dev-up" "k" z1 k)
 	   (p "dev-up" "k" z2 k))
       (= z1 z2))))

   (defrule intro-same-dev-up
     (forall ((z strd) (lk ls locn))
	     (implies
	      (and (p "dev-up" "lk" z lk)
		   (p "dev-up" "ls" z ls))
	      (fact same-dev ls lk))))

   (defrule intro-same-dev-open
     (forall ((z strd) (lk ls locn))
	     (implies
	      (and (p "dev-open" "lk" z lk)
		   (p "dev-open" "ls" z ls))
	      (fact same-dev ls lk))))

   (defrule intro-same-dev-close
     (forall ((z strd) (lk ls locn))
	     (implies
	      (and (p "dev-close" "lk" z lk)
		   (p "dev-close" "ls" z ls))
	      (fact same-dev ls lk))))

   (defrule intro-same-dev-pass
     (forall ((z strd) (lk ls locn))
	     (implies
	      (and (p "dev-pass" "lk" z lk)
		   (p "dev-pass" "ls" z ls))
	      (fact same-dev ls lk))))

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

   ;; Single-threaded registers
   (defrule single-thread-up-up
     (forall ((x y strd) (lk locn))
   	     (implies
   	      (and (p "dev-up" x 5)
   		   (p "dev-up" y 5)
   		   (p "dev-up" "lk" x lk)
   		   (p "dev-up" "lk" y lk))
   	      (or (= x y)
		  (prec x 4 y 1)
   		  (prec y 4 x 1)))))

   (defrule single-thread-up-open
     (forall ((x y strd) (ls locn))
   	     (implies
   	      (and (p "dev-up" x 5)
   		   (p "dev-open" y 4)
   		   (p "dev-up" "ls" x ls)
   		   (p "dev-open" "ls" y ls))
   	      (or (prec x 4 y 1)
   		  (prec y 3 x 1)))))

   (defrule single-thread-up-close
     (forall ((x y strd) (ls locn))
   	     (implies
   	      (and (p "dev-up" x 5)
   		   (p "dev-close" y 4)
   		   (p "dev-up" "ls" x ls)
   		   (p "dev-close" "ls" y ls))
   	      (or (prec x 4 y 1)
   		  (prec y 3 x 1)))))

   (defrule single-thread-open-open
     (forall ((x y strd) (ls locn))
   	     (implies
   	      (and (p "dev-open" x 4)
   		   (p "dev-open" y 4)
   		   (p "dev-open" "ls" x ls)
   		   (p "dev-open" "ls" y ls))
   	      (or (= x y)
   		  (prec x 3 y 1)
   		  (prec y 3 x 1)))))

   (defrule single-thread-ls-open-close
     (forall ((x y strd) (ls locn))
   	     (implies
   	      (and (p "dev-open" x 4)
   		   (p "dev-close" y 4)
   		   (p "dev-open" "ls" x ls)
   		   (p "dev-close" "ls" y ls))
   	      (or (prec x 3 y 1)
   		  (prec y 3 x 1)))))

   (defrule single-thread-close-close
     (forall ((x y strd) (ls locn))
   	     (implies
   	      (and (p "dev-close" x 4)
   		   (p "dev-close" y 4)
   		   (p "dev-close" "ls" x ls)
   		   (p "dev-close" "ls" y ls))
   	      (or (= x y)
   		  (prec x 3 y 1)
   		  (prec y 3 x 1)))))

   (defrule atomic-up-pass
     (forall ((x y strd) (lk locn))
   	     (implies
   	      (and (p "dev-up" x 5)
   		   (p "dev-pass" y 3)
   		   (p "dev-up" "lk" x lk)
   		   (p "dev-pass" "lk" y lk)
   		   (prec x 2 y 1))
   	      (prec x 4 y 1))))

   (defrule dev-up-completes
     (forall ((x strd))
	     (implies
	      (p "dev-up" x 2)
	      (p "dev-up" x 5))))

   (defrule dev-open-completes
     (forall ((x strd))
	     (implies
	      (p "dev-open" x 2)
	      (p "dev-open" x 4))))

   (defrule dev-close-completes
     (forall ((x strd))
	     (implies
	      (p "dev-close" x 2)
	      (p "dev-close" x 4))))

   (defrule dev-pass-completes
     (forall ((x strd))
	     (implies
	      (p "dev-pass" x 2)
	      (p "dev-pass" x 3))))

   (defrule dev-up-atomic1
     (forall ((x z strd) (i1 indx))
	     (implies
	      (and (p "dev-up" z 5)
		   (prec x i1 z 4))
	      (or (= x z)
		  (prec x i1 z 1)))))

   (defrule dev-up-atomic2
     (forall ((x z strd) (i1 indx))
	     (implies
	      (and (p "dev-up" z 5)
		   (prec z 1 x i1))
	      (or (= x z)
		  (prec z 4 x i1)))))

   (defrule dev-open-atomic1
     (forall ((x z strd) (i1 indx))
	     (implies
	      (and (p "dev-open" z 4)
		   (prec x i1 z 3))
	      (or (= x z)
		  (prec x i1 z 1)))))

   (defrule dev-open-atomic2
     (forall ((x z strd) (i1 indx))
	     (implies
	      (and (p "dev-open" z 4)
		   (prec z 1 x i1))
	      (or (= x z)
		  (prec z 3 x i1)))))

   (defrule dev-close-atomic1
     (forall ((x z strd) (i1 indx))
	     (implies
	      (and (p "dev-close" z 4)
		   (prec x i1 z 3))
	      (or (= x z)
		  (prec x i1 z 1)))))

   (defrule dev-close-atomic2
     (forall ((x z strd) (i1 indx))
	     (implies
	      (and (p "dev-close" z 4)
		   (prec z 1 x i1))
	      (or (= x z)
		  (prec z 3 x i1)))))

   (defrule dev-pass-atomic1
     (forall ((x z strd) (i1 indx))
	     (implies
	      (and (p "dev-pass" z 3)
		   (prec x i1 z 2))
	      (or (= x z)
		  (prec x i1 z 1)))))

   (defrule dev-pass-atomic2
     (forall ((x z strd) (i1 indx))
	     (implies
	      (and (p "dev-pass" z 3)
		   (prec z 1 x i1))
	      (or (= x z)
		  (prec z 2 x i1)))))

;;      (defrule leadsto-la
;;        (forall ((z1 z2 strd) (i1 i2 indx))
;;     	     (implies
;;     	      (leads-to z1 i1 z2 i2)
;;     	      (fact la z1 i1 z2 i2)))
;;        (comment this is a rule comment))
;;
;;      (defrule commpair-cp
;;        (forall ((z1 z2 strd) (i1 i2 indx))
;;     	     (implies
;;     	      (comm-pr z1 i1 z2 i2)
;;     	      (fact cp z1 i1 z2 i2)))
;;        (comment this is a rule comment))
;;
;;      (defrule prec-pr
;;        (forall ((z1 z2 strd) (i1 i2 indx))
;;     	     (implies
;;     	      (prec z1 i1 z2 i2)
;;     	      (fact pr z1 i1 z2 i2)))
;;        (comment this is a rule comment))

   ;; (defrule atomic-simpl
   ;;   (forall ((x z strd) (i1 i2 i3 indx))
   ;; 	     (implies
   ;; 	      (and (fact atomic z i1 i2)
   ;; 		   (prec x i3 z i1))
   ;; 	      (or (= x z)
   ;; 		  (prec x i3 z i1)))))

   ;; (defrule atomic-simpl2
   ;;   (forall ((x z strd) (i1 i2 i3 indx))
   ;; 	     (implies
   ;; 	      (and (fact atomic z i1 i2)
   ;; 		   (prec z i1 x i3))
   ;; 	      (or
   ;; 	       (= x z)
   ;; 	       (prec z i1 x i3)))))

  )

(defskeleton atomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand owner-power-dev 2 (k k))
  (deflistener k)
  (uniq-orig k))

(defskeleton atomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  ;; (defstrand owner-power-dev 2 (k k))
  (defstrand dev-pass 4 (k k))
  ;; (uniq-orig k)
  )

(defskeleton atomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand owner-power-dev 2 (k k))
  (defstrand dev-pass 4 (k k))
  (uniq-orig k))

;; (defskeleton atomic-open-closed
;;   (vars (old old1 any mesg) (n n-0 text) (d o name) (k k-0 skey)
;;     (start-ch chan) (ls lk ls-0 lk-0 locn))
;;   (defstrand owner-power-dev 2 (d d) (o o) (k k) (start-ch start-ch))
;;   (defstrand dev-pass 4 (n n) (d d) (o o) (k k) (lk lk) (ls ls))
;;   (defstrand dev-up 6 (old old) (old1 old1) (d d) (o o) (k k)
;;     (start-ch start-ch) (lk lk) (ls ls-0))
;;   (defstrand user-pass 1 (k k))
;;   (defstrand dev-open 4 (any any) (n n-0) (d d) (o o) (k k-0) (lk lk-0)
;;     (ls ls))
;;   (precedes ((0 0) (2 0)) ((2 2) (1 0)) ((2 5) (0 1)) ((3 0) (1 1))
;;     ((4 3) (1 2)))
;;   (uniq-orig n k))
