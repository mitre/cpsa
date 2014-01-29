(herald timestamping-service)

;; Timestamping service as described on Page 76 in Applied
;; Cryptography, Second Edition by Bruce Schneier.

;; This version DOES NOT send the identity of timestamp holder that
;; follows the one sent to the client.  It's a to do.

(defmacro (link)
  (cat alice_1 h_1 t_1 l_1))

(defmacro (timestamp l)
  (enc n alice h alice_1 h_1 t_1 l (privk trent)))

(defprotocol timestamping-service basic
  (defrole client (vars (alice alice_1 trent name)
  			(n data) (h h_1 text) (t_1 l mesg))
    (trace
     (send (cat h alice))
     (recv (timestamp l))))
  (defrole server (vars (alice alice_1 trent name)
			(n data) (h h_1 text) (t_1 l_1 mesg))
    (trace
     (recv (cat (enc (enc (link) (privk trent)) (pubk trent)) h alice))
     (send (cat (timestamp (hash (link)))
		(enc
		 (enc (hash alice h (timestamp (hash (link))) (hash (link)))
		      (privk trent))
		 (pubk trent)))))
    (uniq-orig n))
  (defrole origin (vars (alice alice_1 trent name)
  			(n data) (h h_1 text) (t_1 l_1 text))
    (trace
     (recv (enc (enc n (privk trent)) (pubk trent)))
     (send (enc
	    (enc alice h (timestamp (hash (link))) (hash (link))
		 (privk trent))
	    (pubk trent)))))
  (defrole big-bang (vars (n data) (trent name))
    (trace (send (enc (enc n (privk trent)) (pubk trent))))
    (uniq-orig n)))

(defskeleton timestamping-service
  (vars (trent name) (n_0 data))
  (defstrand client 2 (trent trent))
  (non-orig (privk trent)))
