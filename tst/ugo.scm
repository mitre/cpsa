(herald uniq-gen-and-orig-example
	(comment "Non-executable role examples"))

;;; These two protocols show examples where generation and origination
;;; of asymmetric key pairs lead to shapes that cannot be
;;; implemented.  Note that key pairs must generate or originate at
;;; the same node in a skeleton.

;;; CPSA computes the shapes that would be possible, assuming that the
;;; responder, given u, could magically determine (invk u).
;;; Presumably, the specifier who writes a protocol like this is
;;; committed to this possibility.  I.e. we consider this the
;;; specifier's responsibility to avoid, not CPSA's responsibility to
;;; detect.  

(defprotocol uniq-gen-example basic
  (defrole init
    (vars (u akey) (k skey))
    (trace
     (send (enc u k))
     (recv (invk u))
     (send u))
    (uniq-gen u)
    (non-orig k)
    (comment
     "Instances of this role generate u and (invk u)"
     "at their first event."))
  (defrole resp
    (vars (u akey) (k skey))
    (trace
     (recv (enc u k))
     (send (invk u))
     (recv u))
    (non-orig k)
    (comment
     "Instances of this role appear to generate (invk u)"
     "at their second event.")))

(defskeleton uniq-gen-example
  (vars)
  (defstrandmax resp)
  (comment "How is the responder able to send (invk u)?"))

(defskeleton uniq-gen-example
  (vars (u akey))
  (defstrandmax resp (u u))
  (uniq-gen (invk u))
  (comment "How is the responder able to send (invk u)?"))

(defprotocol uniq-orig-example basic
  (defrole init
    (vars (u akey) (k skey))
    (trace
     (send (enc u k))
     (recv (invk u))
     (send u))
    (uniq-orig u)
    (non-orig k))
  (defrole resp
    (vars (u akey) (k skey))
    (trace
     (recv (enc u k))
     (send (invk u))
     (recv u))
    (non-orig k))
  (comment "Similar to the above, but with uniq-orig instead of uniq-gen."))

(defskeleton uniq-orig-example
  (vars)
  (defstrandmax resp))

(defskeleton uniq-orig-example
  (vars (u akey))
  (defstrandmax resp (u u))
  (uniq-orig (invk u)))
