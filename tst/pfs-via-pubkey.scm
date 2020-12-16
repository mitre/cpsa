(herald pfs-via-pubkey)

(defprotocol pfs-easy basic
  (defrole init
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace
     (send (enc a b new-akey n (privk "sgn" a)))
     (recv (enc (enc a n s (privk "sgn" b)) new-akey))
     (send (privk "sgn" a))))		; compromise signing key subsequently 

  (defrole resp 
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace
     (recv (enc a b new-akey n (privk "sgn" a)))
     (send (enc (enc a n s (privk "sgn" b)) new-akey)))))

(defskeleton pfs-easy
  (vars (new-akey akey) (a b name) (n data) (s text))
  (defstrand init 3 (a a) (b b) (new-akey new-akey) (n n))
  (non-orig (privk "sgn" b) (invk new-akey))
  (uniq-orig (privk "sgn" a) new-akey n))

(defskeleton pfs-easy
  (vars (new-akey akey) (a b name) (n data) (s text))
  (defstrand resp 2 (a a) (new-akey new-akey))
  (non-orig (privk "sgn" a)))

(defskeleton pfs-easy
  (vars (s text) (n data) (a b name) (new-akey akey))
  (defstrand resp 2 (s s) (n n) (a a) (b b) (new-akey new-akey))
  (defstrand init 3 (n n) (a a) (b b) (new-akey new-akey))
  (deflistener s)
  (precedes ((1 0) (0 0)))
  (non-orig (invk new-akey))
  (uniq-orig (privk "sgn" a) s))

