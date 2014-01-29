; missing-contraction
;   The purpose in creating this example was to see if
; CPSA would stubmle when it should find a substitution to
; solve a test node that ultimately unifies the reception
; with something *not* in the escape set.  In this case,
; the receiver's reception is unexplained.  Ordinary
; contraction finds the map that unifies the names a and b
; but (enc a n (pubk b)) is not part of the escape set so
; contraction does not find the substitution that unifies
; n and m.
;   Contraction doesn't work that way but CPSA does have
; another route to finding that shape, but it involves
; augmentation, or more correctly, displacement.  A
; displacement will create a sender that uses m as its n,
; and will unify this with the existing sender, resulting
; effectively in the substitution we were looking for.
;   At the time, CPSA failed to do this, because the map
; that collapses the two sender strands is not a homomorphism
; because it changes the origination point of m on the new
; strand.

(defprotocol missing-contraction basic
  (defrole sender
    (vars (m n text) (a b name))
    (trace
     (send (enc a m (pubk a)))
     (send (enc a n (pubk b)))))
  (defrole receiver
    (vars (m text) (a b name))
    (trace
     (recv (enc a m (pubk b))))))

(defskeleton missing-contraction
  (vars (m text) (a c name))
  (defstrand sender 2 (m m) (a a))
  (defstrand receiver 1 (m m) (a a) (b c))
  (precedes ((0 1) (1 0)))
  (uniq-orig m)
  (non-orig (privk a)))

(defskeleton missing-contraction
  (vars (m text) (a c name))
  (defstrand sender 1 (m m) (a a))
  (deflistener (enc a m (pubk c)))
  (uniq-orig m)
  (non-orig (privk a)))

(defskeleton missing-contraction
  (vars (m text) (a b c name))
  (defstrand sender 2 (m m) (a a) (b b))
  (defstrand receiver 1 (m m) (a a) (b c))
  (precedes ((0 1) (1 0)))
  (uniq-orig m)
  (non-orig (privk a) (privk b)))
