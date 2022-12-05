(herald minipay-rely-guar
	(try-old-strands) 
	(bound 16)
	;; (limit 5000)
	)



(defprotocol minipay-rely-guar basic
  (defrole cust
    (vars (c m b name) (cost amount) (item merchandise)
	  (merc-conf bank-conf btr mtr text) (account acct) (n ncb ncm data))
    (trace
     ;; the customer chooses an item and cost... 
     (guar (fact buy-via c m b item cost n))
     ;; the customer submits item and cost,
     ;; as well as confidential values merc-conf, bank-conf
     ;; to be shared only with the named peer.  A commitment
     ;; will be shared with other peer.
     ;; bank never learns item.
     (send (enc n cost item merc-conf ncm
		(hash n (hash ncb bank-conf))
		(sign (order c m b cost 
			     (enc n cost account bank-conf ncb
				  (hash n (hash ncm item merc-conf))
				  (pubk "enc" b)))
		      (privk "sig" c))
		(pubk "enc" m)))
     
     ;; signed payment info from bank 
     (recv (sign (bconf (hash c m b n cost
			      (hash n (hash ncm item merc-conf)))
			btr mtr)
		 (privk "sig" b)))
     (rely (fact will-transfer c m b cost n mtr btr))

     ;; signed shipping form from merchant
     (recv (sign (mconf (hash c m b n item cost
			      (hash n (hash ncb bank-conf)))
			btr mtr)
		 (privk "sig" m)))
     (rely (fact will-ship c m b item mtr)))
    (facts (neq n ncb) (neq n ncm) (neq ncm ncb))
    )

  (defrole merc
    (vars (c m b name) (cost amount) (item merchandise)
	  (merc-conf bank-conf btr mtr text) (n ncm data)
	  (for-bank bank-conf-commit bank-conf-decommit mesg))
    (trace
     (recv (enc n cost item merc-conf ncm
		bank-conf-commit
		(sign (order c m b cost for-bank)
		      (privk "sig" c))
		(pubk "enc" m)))
     ;; transmit payment request to bank 
     (send (enc (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
			 (cat (sign (order c m b cost for-bank)
				    (privk "sig" c))
			      for-bank))
		 (pubk "enc" b)))
     ;; receive payment offer and decommit for bank-conf 
     (recv (enc bank-conf-decommit 
		(sign (bconf (hash c m b n cost (hash n (hash ncm item merc-conf))) btr mtr)
		      (privk "sig" b))
		(pubk "enc" m)))
     (cheq bank-conf-commit (hash n bank-conf-decommit))
     (rely (and (fact buy-via c m b item cost n)
		(fact will-transfer c m b cost n mtr btr)))

     ;; Now commit to shipping the goods 
     (guar (fact will-ship c m b item mtr))
     ;; return signed info to customer
     (send (sign (bconf (hash c m b n cost (hash n (hash ncm item merc-conf))) btr mtr)
		 (privk "sig" b)))
     (send (sign (mconf (hash c m b n item cost (hash n bank-conf-decommit)) btr mtr)
		 (privk "sig" m))))
    (uniq-orig mtr)
    ;; (facts (neq n ncm))
    )

  (defrole bank
    (vars (c m b name) (cost amount)
	  (merc-conf bank-conf btr mtr text) (merc-conf-decommit mesg) (account acct) (n ncb data))
    (trace
     ;; receive payment requests from merchant and customer,
     ;; including decommit for merc-conf 
     (recv (enc (payreq c m b (hash cost n) merc-conf-decommit mtr
			(cat
			 (sign (order c m b cost
				      (enc n cost account bank-conf ncb
					   (hash n merc-conf-decommit) (pubk "enc" b)))
			       (privk "sig" c))
			 (enc n cost account bank-conf ncb
			      (hash n merc-conf-decommit)
			      (pubk "enc" b))))
		(pubk "enc" b)))
     (rely (exists ((item merchandise))
		   (fact buy-via c m b item cost n)))

     ;; Do not proceed unless customer signature trustworthy      
     ;; Given that, now commit to transferring the funds 
     (guar (and (non (privk "sig" c))
		(fact will-transfer c m b cost n mtr btr)))
     ;; send payment offer 
     (send (enc (hash ncb bank-conf) 
		(sign (bconf (hash c m b n cost (hash n merc-conf-decommit)) btr mtr)
		      (privk "sig" b))
		(pubk "enc" m))))
    (uniq-orig btr)
;;    (facts (neq n ncb))
    )

  (lang (acct atom)
	(amount atom)
	(merchandise atom)
	(sign sign)
	(order (tuple 5))
	(bconf (tuple 3))
	(mconf (tuple 3))
	(payreq (tuple 7))))



(defskeleton minipay-rely-guar
  (vars (c m b name) (cost item merc-conf bank-conf text) (account n data))
  (defstrand cust 3 (c c) (m m) (b b) (n n))
  (uniq-orig n)
  (non-orig (privk "sig" m) (privk "sig" b)
	    (privk "enc" m) (privk "enc" b)))

(defskeleton minipay-rely-guar
  (vars (c m b name) (cost item merc-conf bank-conf text) (account n data))
  (defstrand merc 3 (c c) (m m) (b b))  
  (non-orig (privk "sig" b) (privk "sig" m)
	    (privk "enc" m) (privk "enc" b)))

(defskeleton minipay-rely-guar
  (vars (c m b name) (cost item merc-conf bank-conf text) (account n data))
  (defstrand bank 2 (c c) (m m) (b b) (n n))
  (non-orig (privk "sig" m) (privk "sig" c)
	    (privk "enc" m) (privk "enc" b)))

(defskeleton minipay-rely-guar
  (vars (c m b name) (cost item merc-conf bank-conf text) (account n data))
  (defstrand bank 2 (c c) (m m) (b b) (n n))
  (non-orig (privk "enc" m) (privk "sig" c)))

(defskeleton minipay-rely-guar
  (vars (c m b name) (cost item merc-conf bank-conf text) (account n data))
  (defstrand cust 3 (c c) (m m) (b b) (n n))
  (defstrand merc 3 (c c) (m m) (b b) (n n))
  (defstrand merc 3 (c c) (m m) (b b) (n n))
  (uniq-orig n)
  (non-orig (privk "sig" b)
	    (privk "enc" b)))


(comment
 (defskeleton minipay-rely-guar
   (vars (account acct) (cost amount) (n ncb ncm data) (item merchandise)
	 (bank-conf btr mtr merc-conf mtr-0 text) (c m b name))
   (defstrand bank 2 (merc-conf-decommit (hash ncm item merc-conf))
     (account account) (cost cost) (n n) (ncb ncb) (bank-conf bank-conf)
     (btr btr) (mtr mtr) (c c) (m m) (b b))
   (defstrand cust
     ;; Increase cust to full height
     3
     (account account) (cost cost) (n n) (ncb ncb)
     (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf)
     (c c) (m m) (b b))
   (defstrand merc 2
     (for-bank
      (enc n cost account bank-conf ncb
           (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
     (bank-conf-commit (hash n (hash ncb bank-conf))) (cost cost) (n n)
     (ncm ncm) (item item) (merc-conf merc-conf) (mtr mtr-0) (c c) (m m)
     (b b))
   (precedes ((1 0) (2 0)) ((2 1) (0 0)))
   (non-orig (privk "enc" m) (privk "sig" c)
	     ;; add merchant sig key, bank sig key 
	     (privk "sig" m) (privk "sig" b)) 
   (uniq-orig btr mtr-0 ncm n ncb)
   (facts (neq n ncb) (neq n ncm) (neq ncm ncb))))


(defskeleton minipay-rely-guar
  (vars (c m b name) (cost item merc-conf bank-conf text) (account acct) (n data))
  (defstrand merc 4 (c c) (m m) (b b))  
  (non-orig (privk "sig" b) (privk "sig" m)
	    (privk "enc" m) (privk "enc" b)))

(defskeleton minipay-rely-guar
  (vars (c m b name) (cost item merc-conf bank-conf text) (account acct) (n data))
  (defstrand merc 4 (c c) (m m) (b b))  
  (non-orig (privk "sig" b)))

(defskeleton minipay-rely-guar
  (vars (c m b name) (cost item merc-conf bank-conf text) (account acct) (n data))
  (defstrand merc 1 (c c) (m m) (b b))  
  (non-orig (privk "sig" c)
	    (privk "enc" m)))

(defskeleton minipay-rely-guar
  (vars (c m b name) (cost item merc-conf bank-conf text) (account acct) (n data))
  (defstrand merc 1 (c c) (m m) (b b))  
  (non-orig (privk "sig" c)
	    (privk "enc" m)
	    (privk "enc" b)))
