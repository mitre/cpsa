(herald "Example 1.3 from 1983 Dolev-Yao Paper")

; This protocol, from Example 1.3 in 1983 Dolev-Yao paper, is known to
; be vulnerable to the following attack.

; A->E : {{M}KB, A}KB
; E->B : {{{M}KB, A}KB, E}KB
; B->E : {{{M}KB, A}KE, B}KE
; E->B : {{M}KB, E}KB
; B->E : {{M}KE, B}KE

; So E gets M.

(defprotocol dy basic
  (defrole init (vars (a b name) (m text))
    (trace
     (send (enc (enc m (pubk b)) a (pubk b)))
     (recv (enc (enc m (pubk a)) b (pubk a)))))
  (defrole resp (vars (a b name) (m mesg))
    (trace
     (recv (enc (enc m (pubk b)) a (pubk b)))
     (send (enc (enc m (pubk a)) b (pubk a))))))

(defskeleton dy
  (vars (a b name) (m text))
  (defstrand init 2 (a a) (b b) (m m))
  (uniq-orig m)
  (non-orig (privk a) (privk b)))

(defskeleton dy
  (vars (a b name) (m text))
  (defstrand init 1 (a a) (b b) (m m))
  (deflistener m)
  (uniq-orig m)
  (non-orig (privk a) (privk b)))
