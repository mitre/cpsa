(herald "Signed Encrypted Message Example"
   (comment "Shows examples of key usage of asymmetric keys"))

(defprotocol mult-keys-sig-enc basic
   (defrole init
    (vars (a b name) (n1 n2 text))
    (trace
     (send (enc (enc n1 a (privk "sig" a)) (pubk "enc" b)))
     (recv (enc (enc n1 n2 (privk "sig" b)) (pubk "enc" a)))
     (send (enc (enc n2 (privk "sig" a)) (pubk "enc" b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace
     (recv (enc (enc n1 a (privk "sig" a)) (pubk "enc" b)))
     (send (enc (enc n1 n2 (privk "sig" b)) (pubk "enc" a)))
     (recv (enc (enc n2 (privk "sig" a)) (pubk "enc" b))))))

;;; The initiator point-of-view
(defskeleton mult-keys-sig-enc
   (vars (a b name) (n1 text))
   (defstrand init 3 (a a) (b b) (n1 n1))
   (non-orig (privk "enc" a) (privk "sig" a) (privk "enc" b))
   (uniq-orig n1))

;;; The responder point-of-view trusting only a's signature key
(defskeleton mult-keys-sig-enc
  (vars (a b name) (n2 text))
  (defstrand resp 3 (a a) (b b) (n2 n2))
  (non-orig (privk "sig" a))
  (uniq-orig n2))

;;; The responder point-of-view trusting only a's encryption key
(defskeleton mult-keys-sig-enc
  (vars (a b name) (n2 text))
  (defstrand resp 3 (a a) (b b) (n2 n2))
  (non-orig (privk "enc" a))
  (uniq-orig n2))

;;; The responder point-of-view trusting both of a's keys
(defskeleton mult-keys-sig-enc
  (vars (a b name) (n2 text))
  (defstrand resp 3 (a a) (b b) (n2 n2))
  (non-orig (privk "sig" a) (privk "enc" a))
  (uniq-orig n2))
