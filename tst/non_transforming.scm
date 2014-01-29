; non_transforming.scm --
;  Illustrates a bug.  In the given
; POV, if we try an augmentation with
; (breaker 3), cowt causes a unification
; that makes the 3rd node no longer a
; transforming node, because the same
; message is sent at the 2nd node.

(defprotocol non_transforming basic
  (defrole sender
    (vars (a b text) (B name))
    (trace
      (send (enc a b (pubk B)))
    )
    (uniq-orig a b)
    (non-orig (privk B))
  )
  (defrole recv
    (vars (a b text) (B name))
    (trace
      (recv (enc a (pubk B)))
      (recv (enc b (pubk B)))
    )
  )
  (defrole breaker
    (vars (a b text) (B name))
    (trace
       (recv (enc a b (pubk B)))
       (send (enc a (pubk B)))
       (send (enc b (pubk B)))
    )
  )
)

(defskeleton non_transforming
  (vars (a b c d text) (B B0 B1 name))
  (defstrand recv 2 (a a) (b b) (B B))
  (defstrand sender 1 (a a) (b d) (B B0))
  (defstrand sender 1 (a c) (b b) (B B1))
  (precedes ((1 0) (0 0)) ((2 0) (0 1)))
  (uniq-orig a b)
)
