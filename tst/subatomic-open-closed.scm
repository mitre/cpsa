(herald subatomic-open-closed
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

(defprotocol subatomic-open-closed basic
  (defrole dev-up
    (vars (k skey) (d o name) (old old1 mesg) (start-ch chan) (lk ls locn))
    (trace
     (recv start-ch (cat "power-up" d o k))
     (load lk old) 
     (load ls old1)
     (stor ls (dev-state-closed d o))
     (stor lk (dev-key-state d o k))
     (send (enc "up" k)))
    (auth start-ch)
    (critical-sections (1 4)))

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
     (send n))
    (critical-sections (1 3)))

  (defrole dev-close
    (vars (k skey) (n text) (any mesg) (d o name) (lk ls locn))
    (trace
     (recv (enc "close" d o n k))
     (load lk (dev-key-state d o k))
     (load ls (dev-state-any d o any))
     (stor ls (dev-state-closed d o))
     (send n))
    (critical-sections (1 3)))

  (defrole dev-pass
    (vars (k skey) (n text) (d o name) (lk ls locn))
    (trace
     (load lk (dev-key-state d o k))
     (load ls (dev-state-opened d o))
     (recv (enc "may I pass" k))
     (send (enc "you may pass" n k)))
    (uniq-orig n)
    (critical-sections (0 1)))

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
	     (gen-st (dev-key-state d o k)))))

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

   ;; Single-threaded registers omitted

;      (defrule atomic-cause-dev-pass
;        (forall
;         ((z1 z2 strd) (i indx))
;         (implies (and (p "dev-pass" z1 2)
;   		    (prec z2 i z1 1))
;   	       (or (= z1 z2)
;   		   (prec z2 i z1 0)))))
;   
;      (defrule atomic-cause-dev-open
;        (forall
;         ((z1 z2 strd) (i indx))
;         (implies (and (p "dev-open" z1 3)
;   		    (prec z2 i z1 2))
;   	       (or (= z1 z2)
;   		   (prec z2 i z1 1)))))
   
  )

(defskeleton subatomic-open-closed
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand owner-power-dev 2 (k k))
  (deflistener k)
  (uniq-orig k)
  (facts (no-state-split)))

(defskeleton subatomic-open-closed 
  (vars (k skey) (d o name) (n text) (start-ch chan))
  ;; (defstrand owner-power-dev 2 (k k))
  (defstrand dev-pass 4 (k k))
  ;; (uniq-orig k)
   (facts (no-state-split))
  )

(defskeleton subatomic-open-closed 
  (vars (k skey) (d o name) (n text) (start-ch chan))
  (defstrand owner-power-dev 2 (k k))
  (defstrand dev-pass 4 (k k))
  (uniq-orig k)
  (facts (no-state-split)))

;; (defskeleton subatomic-open-closed
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

