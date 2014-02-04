(herald wrap-decrypt)

(defprotocol wrap-decrypt basic
  (defrole make
    (vars (k skey))
    (trace
     (sync (cat "make" (hash k)))
     (send (hash k)))
    (pen-non-orig k))
  (defrole set-wrap
    (vars (k skey))
    (trace
     (sync (cat "set-wrap" (hash k)))))
  (defrole set-decrypt
    (vars (k skey))
    (trace
     (sync (cat "set-decrypt" (hash k)))))
  (defrole wrap
    (vars (k0 k1 skey))
    (trace
     (recv (hash k0))
     (recv (hash k1))
     (sync (cat "wrap" (hash k0) (hash k1)))
     (send (enc k0 k1))))
  (defrole decrypt
    (vars (x mesg) (k skey))
    (trace
     (recv (enc x k))
     (recv (hash k))
     (sync (cat "decrypt" (hash k)))
     (send x))))

(defskeleton wrap-decrypt
  (vars (k skey))
  (deflistener k)
  (defstrand make 2 (k k))
  (defstrand wrap 4 (k0 k) (k1 k))
  (defstrand decrypt 4 (x k) (k k))
  (precedes ((1 1) (2 0)) ((2 3) (3 0)) ((3 3) (0 0)))
  (comment "desired shape"))

(defskeleton wrap-decrypt
  (vars (k skey))
  (deflistener k)
  (defstrand make 2 (k k)))

(defskeleton wrap-decrypt
  (vars (k k1 skey))
  (deflistener k)
  (defstrand wrap 4 (k0 k) (k1 k1))
  (defstrand make 2 (k k))
  (defstrand make 2 (k k1))
  (precedes ((1 3) (0 0)) ((2 1) (1 0)) ((3 1) (1 1))))
