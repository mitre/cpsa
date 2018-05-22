(herald expand (expand) (comment "test macro expansion"))

(defmacro (altenc t k)
  (enc t k))

(defmacro (altcat a b)
  (^ a b))

(defprotocol expand basic
  (defrole init
    (vars (t text) (k skey))
    (trace
     (send (altenc t k))
     (recv (cat (altcat t k))))))

(defskeleton expand
  (vars)
  (defstrand init 2))
