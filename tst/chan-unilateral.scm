(herald chan-unilateral)

;; Unilateral authentication using channels with differing assumptions.

(defprotocol unilateral basic
  (defrole init
     (vars (n text) (ch chan))
     (trace
      (send ch n)
      (recv n))
     (uniq-orig n))
  (defrole resp
     (vars (n text) (ch chan))
     (trace
      (recv ch (cat ch n))
      (send n)))
  (comment "Unilateral protocol using channels with differing assumptions"))

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
