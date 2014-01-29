;; This file demonstrates a way to model DH keys in a limited way
;; within the Basic Crypto Algebra.  The idea is the following:
;; the pair (x, g^x) is represented as ((invk x), x), and similarly
;; for (y, g^y).  The owner of (invk x) computes (hash (invk x) y) and
;; the owner of (invk y) computes (hash x (invk y)).  We add an auxiliary
;; role (other protocols may need more auxiliary roles) that serves
;; to transform encryptions using (hash (invk x) y) into encryptions
;; using (hash x (invk y)).

;; This has the advantage that the adversary cannot decrypt these
;; messages if he does not have either (invk x) or (invk y).  However,
;; the presence of the auxiliary role makes it possible for the
;; adversary to decrypt the message by knowing either (invk x) or
;; (invk y).

;; It is currently unclear how well this solution will scale to larger
;; protocols which may need more auxiliary roles.  This also completely
;; ignores algebraic properties of DH and hence it excludes algebraic
;; attacks from consideration.

(herald "DH Hack" (bound 15))

(defprotocol DH_hack basic
  (defrole init1
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
     (send (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    (uniq-orig cek d x))
  (defrole resp
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
     (recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
  (defrole commute
    (vars (gcs name) (cek skey) (x y akey) (d data) )
    (trace
     (recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
     (send (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs))))

 (defskeleton DH_hack
  (vars (x y akey))
  (defstrand resp 1 (x x) (y y))
  (non-orig (invk x) (invk y)))

 (defskeleton DH_hack
  (vars (cek skey) (x y akey))
  (defstrand resp 1 (cek cek) (x x))
  (non-orig (invk x)))

(defskeleton DH_hack
  (vars (cek skey) (x y akey))
  (defstrand resp 1 (cek cek) (y y))
  (non-orig (invk y)))

(defskeleton DH_hack
  (vars (cek skey) (x y akey))
  (defstrand resp 1 (cek cek) (x x) (y y))
  (deflistener cek)
  (non-orig (invk x) (invk y)))

 (defskeleton DH_hack
  (vars (cek skey) (x y akey))
  (defstrand resp 1 (cek cek) (x x))
  (deflistener cek)
  (non-orig (invk x)))

(defskeleton DH_hack
  (vars (cek skey) (x y akey))
  (defstrand resp 1 (cek cek) (y y))
  (deflistener cek)
  (non-orig (invk y)))
