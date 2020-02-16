(comment "CPSA 4.2.3")
(comment "Expanded macros")

(herald expand (expand) (comment "test macro expansion"))

(defprotocol expand basic
  (defrole init
    (vars (t text) (k skey))
    (trace (send (enc t k)) (recv (cat t k)))))

(defskeleton expand (vars) (defstrand init 2))
