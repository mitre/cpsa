(herald "Kelly's 64-shape protocol" (bound 10))

(defprotocol kelly64 basic
  (defrole client
    (vars (C name) (A name) (S name) (AIKC name) (NC text)
	  (hello text) (Quote text) (mc text) (request text)
	  (response text) (Check text) (P2 text))
    (trace
     (send (cat C A hello))
     (recv (cat A C NC))
     (send (cat C A (enc
		     (cat Quote mc NC
			  (enc
			   (pubk C)
			   (privk C)))
		     (privk AIKC))
		(enc
		 (pubk C)
		 (privk C))))
     (send (cat C S
		(enc (cat request request)
		     (privk C))))
     (recv (cat S C
		(enc response
		     (privk S))))
     (send (cat C A Check (pubk S)))
     (recv (cat A C
		(enc (cat P2 (pubk S))
		     (privk A)))))
    (non-orig (privk C) (privk AIKC) (privk A))
    )
  ;;   non = (privk(C);privk(AIKC);privk(A));
  ;;   uniq = ();

  (defrole appraiser
    (vars (C name) (A name) (S name) (AIKS name) (AIKC name)
	  (NS text) (NC text) (hello text)(Quote text)
	  (ms text)(mc text)(Check text)(P1 text)(P2 text))
    (trace

     (recv (cat S A hello))
     (send (cat A S NS))
     (recv (cat S A
		(enc
		 (cat Quote ms NS
		      (enc (pubk S)
			   (privk S)))
		 (privk AIKS))
		(enc
		 (pubk S)
		 (privk S))))
     (recv (cat C A hello))
     (send (cat A C NC))
     (recv (cat C A (enc
		     (cat Quote mc NC (enc
				       (pubk C)
				       (privk C)))
		     (privk AIKC))
		(enc
		 (pubk C)
		 (privk C))))
     (recv (cat S A  Check (pubk C)))
     (send (cat A S (enc
		     (cat P1 (pubk C))
		     (privk A))))
     (recv (cat C A Check (pubk S)))
     (send (cat A C (enc
		     (cat P2 (pubk S))
		     (privk A))))
     )
    (non-orig (privk A) (privk AIKS) (privk AIKC))
    (uniq-orig NS NC)
    ;;   non = (privk(A);privk(AIKS);privk(AIKC));
    ;;   uniq = (NS;NC);
    )

  (defrole server
    (vars (C name) (A name) (S name) (AIKS name) (NS text)
	  (hello text) (Quote text) (ms text) (request text)
	  (Check text) (P1 text) (response text))
    (trace
     ;;   non = (privk(S);privk(AIKS);privk(A));
     ;;  uniq = ();

     (send (cat S A hello))
     (recv (cat A S NS))
     (send (cat S A (enc
		     (cat Quote ms NS (enc
				       (pubk S)
				       (privk S)))
		     (privk AIKS))
		(enc
		 (pubk S)
		 (privk S))))
     (recv (cat C S (enc
		     (cat request request)
		     (privk C))))
     (send (cat S A Check (pubk C)))
     (recv (cat A S (enc
		     (cat P1 (pubk C))
		     (privk A))))
     (send (cat S C (enc
		     response
		     (privk S))))
     )
    (non-orig (privk S) (privk AIKS) (privk A))
    )

  )

(defskeleton kelly64
  (vars (C name) (A name) (S name) (AIKC name) (NC text)
	  (hello text) (Quote text) (mc text) (request text)
	  (response text) (Check text) (P2 text))
  (defstrand client 7 (C C) (A A) (S S) (AIKC AIKC)
    (NC NC) (hello hello) (Quote Quote) (mc mc)
    (request request) (response response) (Check Check) (P2 P2)))

(defskeleton kelly64
  (vars (C name) (A name) (S name) (AIKC name) (NC text)
	  (hello text) (Quote text) (mc text) (request text)
	  (response text) (Check text) (P1 text))
  (defstrand server 7 ))

(defskeleton kelly64
(vars)
  (defstrand appraiser 10))
