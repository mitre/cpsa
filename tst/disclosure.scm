;;; Here's a protocol where there are two ways for the init strand to
;;; be satisfied.  The responder can use the key to extract that
;;; nonce.  Or else the adversary can get the key from the init's last
;;; send, and use that in *the next* session to extract the nonce
;;; without the responder's help.

;;; This is a simplest example in which CPSA needs to introduce a
;;; listener to explore the possibility that the adversary can do the
;;; decryption.  It certainly illustrates that the generalization
;;; steps that discard listeners are a natural part of finding the
;;; minimal shapes.

(herald disclosure)

(defprotocol disc basic
  (defrole init
    (vars (a b name) (k skey) (n text))
    (trace
     (send (enc a b n k))
     (recv n)
     (send k))
    (pen-non-orig k))

  (defrole resp
    (vars (a b name) (k skey) (n text))
    (trace
     (recv (enc a b n k))
     (send n))))

(defskeleton disc
  (vars (n text))
  (defstrand init 2 (n n))
  (uniq-orig n))
