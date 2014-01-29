(herald "Needham-Schroeder-Lowe Protocol with symmetric encryption")

(defprotocol nslsk basic
  (defrole init (vars (a b name) (n text) (k skey) (t text))
    (trace
     (send (enc n a (pubk b)))
     (recv (enc n k b (pubk a)))
     (send (enc t k))))
  (defrole resp (vars (b a name) (n text) (k skey) (t text))
    (trace
     (recv (enc n a (pubk b)))
     (send (enc n k b (pubk a)))
     (recv (enc t k)))))

(defskeleton nslsk
  (vars (a name) (k skey))
  (defstrand resp 3 (a a) (k k))
  (non-orig (privk a))
  (uniq-orig k))

(defskeleton nslsk
  (vars (b name) (n text))
  (defstrand init 3 (b b) (n n))
  (non-orig (privk b))
  (uniq-orig n))

;; Use a tag as a term.

(defprotocol nslsk-tag-term basic
  (defrole init (vars (a b name) (n text) (k skey))
    (trace
     (send (enc n a (pubk b)))
     (recv (enc n k b (pubk a)))
     (send (enc "t" k))))
  (defrole resp (vars (b a name) (n text) (k skey))
    (trace
     (recv (enc n a (pubk b)))
     (send (enc n k b (pubk a)))
     (recv (enc "t" k)))))

(defskeleton nslsk-tag-term
  (vars (a name) (k skey))
  (defstrand resp 3 (a a) (k k))
  (non-orig (privk a))
  (uniq-orig k))

(defskeleton nslsk-tag-term
  (vars (b name) (n text))
  (defstrand init 3 (b b) (n n))
  (non-orig (privk b))
  (uniq-orig n))
