;;; Envelope protocol using sends a standins for transition label
;;; events.  This version of the protocol allows alice to extend an
;;; arbitrary value with the nonce, rather than the boot value.

(herald "Envelope Protocol" (bound 20) (check-nonces))

;;; Encoding of a PCR extend operation
(defmacro (extend val old)
  (hash val old))

;; This is the refusal token
(defmacro (refuse n pcr v k aik)
  (enc "quote" (extend "refuse" (extend n pcr)) (enc v k) aik))

(defprotocol envelope basic

  ;; Power on sets the TPM to the boot state
  (defrole tpm-power-on
    (vars)
    (trace
     (sync "boot")))

  ;; TPM Quote has a fake event to deal with the fact that a variable
  ;; of sort mesg must be acquired.
  (defrole tpm-quote
    (vars (nonce pcr mesg) (aik akey))
    (trace
     (recv (cat "quote" nonce))
     (recv pcr)				; Fake event!
     (sync (cat "observe" pcr))
     (send (enc "quote" pcr nonce aik)))
    (non-orig aik)
    (priority (1 0)))			; Don't solve fake nodes

  ;; The extend command occurs only within an encrypted session.  We
  ;; assume some session key already exists
  (defrole tpm-extend-enc
    (vars (value mesg) (esk skey) (tne tno data)
	  (tpmkey akey))
    (trace
     (recv (cat "establish transport"
		tpmkey (enc esk tpmkey)))
     (send (cat "establish transport" tne))
     (recv (cat "execute transport"
		(cat "extend" (enc value esk))
		tno "false"
		(hash esk (hash "execute transport"
				(hash "extend"
				      (enc value esk)))
				tne tno "false")))
     (sync (cat "extend" value)))
    (uniq-orig tne)
    (non-orig (invk tpmkey)))

  ;; This role creates a key whose use is restricted to a requested
  ;; pcr value (since we only model one pcr).  It doesn't create or
  ;; change any TPM state.
  (defrole tpm-create-key
    (vars (k aik akey) (pcr mesg) (esk skey))
    (trace
     (recv (enc "create key" pcr esk)) ;; encryption prevents weird shapes
     (send (enc "created" k pcr aik)));; no tpm state is set
    (uniq-orig k)
    (non-orig (invk k) aik esk))

  ;; This role receives an encryption and a previously made key
  ;; structure that restricts the decryption key to be used with a
  ;; certain pcr value.  It retrieves the current value and checks
  ;; that it matches before decrypting.
  (defrole tpm-decrypt
    (vars (m pcr mesg) (k aik akey))
    (trace
     (recv (cat "decrypt" (enc m k)))
     (recv (enc "created" k pcr aik))
     (sync (cat "observe" pcr))
     (send m))
    (non-orig aik))

  ;; Alice extends a pcr with a fresh nonce in an encrypted session.
  ;; She has the TPM create a new key whose use is bound to the hash
  ;; of pcr value she just created with the string "obtain".  She then
  ;; encrypts her fresh secret with this newly created key.  This role
  ;; has a fake reception event to deal with he fact that pcr must be
  ;; acquired.
  (defrole alice
    (vars (v tne tno data) (esk1 esk skey) (k aik tpmkey akey)
	  (n text) (pcr mesg))
    (trace
     (send (cat "establish transport"
		tpmkey (enc esk tpmkey)))
     (recv (cat "establish transport" tne))
     (send (cat "execute transport"
		(cat "extend" (enc n esk))
		tno "false"
		(hash esk (hash "execute transport"
				(hash "extend"
				      (enc n esk)))
				tne tno "false")))
     (recv pcr)				; Fake event
     (send (enc "create key" (extend "obtain" (extend n pcr)) esk1))
     (recv (enc "created" k (extend "obtain" (extend n pcr)) aik))
     (send (enc v k)))
    (uniq-orig n v tno esk)
    (non-orig aik esk1 (invk tpmkey))))

;;; Initial skeleton
(defskeleton envelope
  (vars (v data) (k aik akey) (n text) (pcr mesg))
  (deflistener (refuse n pcr v k aik))
  (deflistener v)
  (defstrand alice 7 (n n) (pcr pcr) (v v) (k k) (aik aik)))
