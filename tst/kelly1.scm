;;An attestation protocol containing a client, a server, and an appraiser.

;;The client is attempting to verify that the server he receives his
;;content from is the server he wishes to communicate with, and that the
;;server meets some policy.

;;The appraiser acquires measurements from the server to determine the
;;policy, and passes the resulting policy on to the client. The server's
;;public key is used to identify the server.

;;The server is verifying nothing about his surroundings, and will
;;answer both measurement and content inquiries from anyone.

;;When analyzing this protocol, it is assumes that the client knows some
;;appraiser he trusts; the client analysis should contain non privk(A).

(defprotocol kelly1 basic

  (defrole client
    (vars (C name) (A name) (S name) (Ns text) (request text) (Check text)  (policy text) (response text))
    (trace
     (send (cat C S request))
     (recv (cat S C (enc (cat response Ns)
			 (privk S))))
     (send (cat C A Check (pubk S)))
     (recv (cat A C (enc (cat policy (pubk S) Ns)
			 (privk A))))
      )
    )

  (defrole appraiser
    (vars (C name) (A name) (S name) (N text) (Ns text) (hello text)
	  (Quote text) (measurements text) (Check text) (policy text)
	  (AIK name))
    (trace
     (recv (cat S A hello))
     (send (cat A S N))
     (recv (cat S A
		(enc
		 (cat Quote measurements N Ns (pubk S))
		 (privk AIK))
		(pubk S)))
     (recv (cat C A Check (pubk S)))
     (send (cat A C (enc (cat policy (pubk S) Ns)
			 (privk A))))
      )
    (non-orig (privk A) (privk AIK))
    (uniq-orig N)
    )

  (defrole server
    (vars (C name) (A name) (S name) (N text) (Ns text) (hello text)
	  (Quote text) (measurements text) (request text) (response text)
	  (AIK name))
   (trace
      (send (cat S A hello))
      (recv (cat A S N))
      (send (cat S A
		 (enc
		  (cat Quote measurements N Ns (pubk S))
		  (privk AIK))
		 (pubk S)))
      (recv (cat C S request))
      (send (cat S C (enc (cat response Ns)
			  (privk S))))
      )
   (non-orig (privk S) (privk AIK))
   (uniq-orig  Ns)
   )
)

(defskeleton kelly1
  (vars (A name))
  (defstrand client 4 (A A))
  (non-orig (privk A))
  )
