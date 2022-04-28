(herald dhstatic-state
	(algebra diffie-hellman)
	(bound 16))

(defprotocol dhstatic-state diffie-hellman
  (defrole cert
    (vars (subj ca name) (serial data) (galpha mesg))
    (trace
     (recv (sig (cert-req subj galpha ca) (privk "sig" subj)))
     (send (sig (cert subj galpha ca serial)
		(privk "sig" ca))))
    (uniq-orig serial)
    (comment "Certificate Authority"))

  (defrole get-cert
    (vars (self ca name) (serial data) (ra rndx)
	  (static-key locn) (ignore mesg))
    (trace
     (send (sig (cert-req self (exp (gen) ra) ca) (privk "sig" self)))
     (recv (sig (cert self (exp (gen) ra) ca serial)
		(privk "sig" ca)))
     (load static-key ignore)
     (stor static-key (cat "privkey" self ra serial ca)))

    (uniq-gen ra)
    (comment "Get certified"))

  (defrole init
    (vars (a b ca name) (ra rndx) (serial-a serial-b data)
	  (galpha base) (n text) (static-key locn))
    (trace
     (load static-key (cat "privkey" a ra serial-a ca))
     (recv (sig (cert b galpha ca serial-b)
		(privk "sig" ca)))
     (send (enc n a b serial-a serial-b (exp galpha ra)))
     (recv n))
    (uniq-orig n)
    (gen-st (cat "privkey" a ra serial-a ca))
    (facts (neq a b))
    (comment "Initiator is A"))

  (defrole resp
    (vars (a b ca name) (rb rndx) (serial-b serial-a data)
	  (galpha base) (n text) (static-key locn))
    (trace
     (load static-key (cat "privkey" b rb serial-b ca))
     (recv (sig (cert a galpha ca serial-a)
		(privk "sig" ca)))
     (recv (enc n a b serial-a serial-b (exp galpha rb)))
     (send n))
    (facts (neq a b))
    (gen-st (cat "privkey" b rb serial-b ca))
    (comment "Responder is B"))

  (lang (cert-req (tupl 3))
	(cert (tupl 4))
	(sig sign)))

(defskeleton dhstatic-state
  (vars (ca b name))
  (defstrand init 4 (ca ca) (b b))
  (non-orig (privk "sig" ca) (privk "sig" b)))

(defskeleton dhstatic-state
  (vars (ca a name))
  (defstrand resp 4 (ca ca) (a a))
  (non-orig (privk "sig" ca) (privk "sig" a)))
