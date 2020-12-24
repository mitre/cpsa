;; This protocol has two roles that use a key and its inverse
;; inconsistently.  If one follows the convention that (enc n k)
;; represents an encryption and (enc n (invk k)) represents a digital
;; signature, the two roles clash.

(defprotocol bad-unilateral basic
  (defrole init
    (vars (ch chan) (n text) (k akey))
    (trace
     (send ch (enc n k))
     (recv ch n))
    (uniq-orig n)
    (inputs ch k)
    (outputs n))
  (defrole resp
    (vars (ch chan) (n text) (k akey))
    (trace
     (recv ch (enc n (invk k)))
     (send ch n))
    (inputs ch k)
    (outputs n)))

(defskeleton bad-unilateral
  (vars (k akey))
  (defstrand init 2 (k k))
  (non-orig (invk k)))

(defskeleton bad-unilateral
  (vars (n text) (k akey))
  (defstrand resp 2 (n n) (k k))
  (pen-non-orig n)
  (non-orig k))
