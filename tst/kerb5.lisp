;; Kerberos 5 specification, taken from
;; http://www.lsv.ens-cachan.fr/spore/kerberos.html
;;
;; Ku in the original document has become pubk/privk U.
;; Since we cannot confirm with CPSA that T1 is between T1start and T1expire,
;; and since the purpose of T1 is to have a defined relationship with T1start
;; and T1expire, I am replacing T1 with (cat T1start T1expire). Ditto with T2.

(defprotocol kerb5 basic

  ;; U is the client's user (and, approximately, its principal.)
  (defrole client
    (vars (U name) (G name) (L1 text) (N1 text) (C name) (S name)
	  (L2 text) (N2 text) (Kcg skey) (T1start text) (T1expire text)
	  (Kag skey) (Kgs skey) (T2start text) (T2expire text)
	  (Kcs skey))
    (trace
     (send (cat U G L1 N1))
     (recv (cat U
		(enc (cat U C G Kcg T1start T1expire) Kag)
		(enc (cat G Kcg T1start T1expire) (pubk U))))
     (send (cat S
		L2
		N2
		(enc (cat U C G Kcg T1start T1expire) Kag)
		(enc (cat C T1start T1expire) Kcg)))
     (recv (cat U
		(enc (cat U C S Kcs T2start T2expire) Kgs)
		(enc (cat S Kcs T2start T2expire N2) Kcg)))
     (send (cat (enc (cat U C S Kcs T2start T2expire) Kgs)
		(enc (cat C T2start T2expire) Kcs)))
     (recv (enc (cat T2start T2expire) Kcs))
     )
    (uniq-orig N1 N2)
    (non-orig (privk U))
    )

;; A is the key distribution authority's principal; never used explicitly
;; Kag is a long-term shared key between A and G.
;; Kcg is the session key to be shared by C and G, created by A.
  (defrole authority
    (vars (U name) (G name) (C name) (L1 text) (N1 text)
	  (T1start text) (T1expire text) (Kag skey) (Kcg skey))
    (trace
     (recv (cat U G L1 N1))
     (send (cat U
		(enc (cat U C G Kcg T1start T1expire) Kag)
		(enc (cat G Kcg T1start T1expire) (pubk U))))
     )
    (uniq-orig Kcg)
    (non-orig Kag)
    )

;; G is the ticket granting server's principal.
;; Kag is a long-term shared key between A and G.
;; Kgs is a long-term shared key between G and S.
  (defrole granter
       (vars (U name) (G name) (C name) (S name) (L2 text) (N2 text)
	  (Kcg skey) (T1start text) (T1expire text) (Kag skey)
	  (Kgs skey) (T2start text) (T2expire text) (Kcs skey))
       (trace
	(recv (cat S
		   L2
		   N2
		   (enc (cat U C G Kcg T1start T1expire) Kag)
		   (enc (cat C T1start T1expire) Kcg)))
	(send (cat U
		   (enc (cat U C S Kcs T2start T2expire) Kgs)
		   (enc (cat S Kcs T2start T2expire N2) Kcg)))
	)
       (uniq-orig Kcs)
       (non-orig Kgs Kag)
    )

;; S is the principal of the server that C wishes to communicate with
;; Kgs is a long-term shared key between G and S.
  (defrole server
    (vars (U name) (C name) (S name) (Kgs skey) (T2start text)
	  (T2expire text) (Kcs skey))
    (trace
     (recv (cat (enc (cat U C S Kcs T2start T2expire) Kgs)
		(enc (cat C T2start T2expire) Kcs)))
     (send (enc (cat T2start T2expire) Kcs))
     )
    (uniq-orig )
    (non-orig Kgs)
    )

)

 (defskeleton kerb5
    (vars )
    (defstrand server 2)
    )
