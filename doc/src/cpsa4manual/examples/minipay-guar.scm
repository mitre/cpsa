(herald minipay-guar
	(try-old-strands)
	(bound 16)
	;; (limit 5000)
	)

(defprotocol minipay-guar basic
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

     ;; signed shipping form from merchant
     (recv (sign (mconf (hash c m b n item cost
			      (hash n (hash ncb bank-conf)))
			btr mtr)
		 (privk "sig" m))))
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

(defgoal minipay-guar
  (forall
   ((z strd) (c m b name) (cost amount) (n data) (mtr btr text))
   (implies
    (and (p "cust" z 2)
	 (p "cust" "c" z c)
	 (p "cust" "m" z m)
	 (p "cust" "b" z b)
	 (p "cust" "cost" z cost)
	 (p "cust" "n" z n)
	 (p "cust" "mtr" z mtr)
	 (p "cust" "btr" z btr)
	 (non (privk "sig" b)))
    (fact will-transfer c m b cost n mtr btr))))

(defgoal minipay-guar
  (forall
   ((z strd) (c m b name) (item merchandise) (n data) (mtr btr text))
   (implies
    (and (p "cust" z 3)
	 (p "cust" "c" z c)
	 (p "cust" "m" z m)
	 (p "cust" "b" z b)
	 (p "cust" "item" z item)
	 (p "cust" "n" z n)
	 (p "cust" "mtr" z mtr)
	 (p "cust" "btr" z btr)
	 (non (privk "sig" m)))
    (fact will-ship c m b item mtr))))

(defgoal minipay-guar
  (forall
   ((z strd) (c m b name) (item merchandise) (cost amount) (n data) (mtr btr text))
   (implies
    (and (p "merc" z 3)
	 (p "merc" "c" z c)
	 (p "merc" "m" z m)
	 (p "merc" "b" z b)
	 (p "merc" "item" z item)
	 (p "merc" "cost" z cost)
	 (p "merc" "n" z n)
	 (p "merc" "mtr" z mtr)
	 (p "merc" "btr" z btr)
	 (non (privk "sig" b)))
    (and (fact will-transfer c m b cost n mtr btr)
	 (fact buy-via c m b item cost n)))))

(defgoal minipay-guar
  (forall
   ((z strd) (c m b name) (cost amount) (n data))
   (implies
    (and (p "bank" z 1)
	 (p "bank" "c" z c)
	 (p "bank" "m" z m)
	 (p "bank" "b" z b)
	 (p "bank" "cost" z cost)
	 (p "bank" "n" z n)
	 (non (privk "sig" c)))
    (exists ((item merchandise))
	    (fact buy-via c m b item cost n)))))
