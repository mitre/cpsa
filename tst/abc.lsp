;;  Simple example of A-B-C cascading.
;;  Input should be a dead skeleton.
;;  Cascading occurs because roles A, B, and C seem to
;;  create progress, but nothing can ever produce their input in the
;;  correct form.

(defprotocol abc basic
  (defrole init (vars (x text) (k skey))
    (trace
     (send (enc x k))
     (recv (enc x x k)))
    (uniq-orig x)
    (non-orig k))
  (defrole A (vars (x text) (k skey))
    (trace
     (recv (enc "A" x k))
     (send (enc x x k))))
  (defrole B (vars (x text) (k skey))
    (trace
     (recv (enc "B" x k))
     (send (enc x x k))))
  (defrole C (vars (x text) (k skey))
    (trace
     (recv (enc "C" x k))
     (send (enc x x k))))
)

(defskeleton abc
  (vars (x text) (k skey))
  (defstrand init 2 (x x) (k k)))
