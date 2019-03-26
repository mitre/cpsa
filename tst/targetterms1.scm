;; Solution requires the use of target terms in the solved filter.

;; The protocol is strange because the initiator sends out two texts
;; that turn out must be the same.

(defprotocol targetterms basic
  (defrole init (vars (a skey) (n1 n2 text) (k akey))
    (trace
     (send (enc n1 (enc a n2 k) k))
     (recv (enc a n1 k))))

  (defrole resp (vars (n1 text) (m mesg) (k akey))
    (trace
     (recv (enc n1 m k))
     (send m))))

(defskeleton targetterms
  (vars (n1 text) (k akey))
  (defstrand init 2 (n1 n1) (k k))
  (non-orig (invk k))
  (uniq-orig n1))
