(herald chan-unilateral)

;; Unilateral authentication using channels with differing assumptions.

(defprotocol unilateral basic
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
      (recv ch (enc n k))
      (send ch n))
     (inputs ch (invk k))
     (outputs n))
  (comment "Unilateral protocol with inputs and outputs"))

(defskeleton unilateral
   (vars (ch chan))
   (defstrand init 2 (ch ch)))

(defskeleton unilateral
   (vars (ch chan))
   (defstrand init 2 (ch ch))
   (auth ch))

(defskeleton unilateral
   (vars (ch chan))
   (defstrand init 2 (ch ch))
   (conf ch))

(defskeleton unilateral
   (vars (ch chan))
   (defstrand init 2 (ch ch))
   (auth ch)
   (conf ch))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand resp 2 (n n) (ch ch))
  (pen-non-orig n))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand resp 2 (n n) (ch ch))
  (pen-non-orig n)
  (auth ch))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand resp 2 (n n) (ch ch))
  (pen-non-orig n)
  (conf ch))

(defskeleton unilateral
  (vars (n text) (ch chan))
  (defstrand resp 2 (n n) (ch ch))
  (pen-non-orig n)
  (auth ch)
  (conf ch))
