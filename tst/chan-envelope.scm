(herald "Envelope Protocol With Channels" (bound 15))

;;; This file analyzes the Envelope Protocol using three rules sets.
;;; For each rule set, it checks three scenarios.  In every scenario,
;;; an Alice strand runs to completion.  In the first scenario, the
;;; obtain token is listened for.  In the second, a listener for the
;;; refusal token is included.  In the third scenario, both listeners
;;; are included.  The third scenario should be impossible, but rules
;;; are required to accurately model state.
;;;
;;; The first rule set is empty and the answer to the third scenario
;;; shows a case is which the TPM's PCR state splits.  The second rule
;;; set forces TPM extends to be linearly ordered.  However, in this
;;; case, there are two TPMs when there should be one as Alice uses
;;; one TPM storage key to communicate with both TPMs.  The final rule
;;; set includes a rule about storage keys and thus accurately models
;;; state.
;;;
;;; Macros are used to avoid copying roles and scenarios.

;; This is the refusal token
(defmacro (refuse n v k aik)
  (enc "quote" (hash (hash "0" n) "refuse") (enc v k) aik))

;;; This protocol tracks the TPM's PCR state
;;; by sending a message with the current PCR
;;; value encrypted by a hashed secret key.
;;; The hash is used to prevent a confusion with
;;; the key for an encrypted session.

(defmacro (roles)
  (^
   ;; Power on sets the pcr to 0
   (defrole tpm-power-on
     (vars (c chan))
     (trace
      (recv "power on")
      (send c "0"))
     (conf c)
     (auth c))

   ;; The extend command takes the value to
   ;; extend and the current PCR value (in the
   ;; form of a message encrypted with the special
   ;; PCR state key) and produces the hash of the
   ;; two values (by sending it encrypted in the
   ;; special PCR state key).
   (defrole tpm-extend
     (vars (value current-value mesg) (c chan))
     (trace
      (recv (cat "extend" value))
      (recv c current-value)		  ;; MSR lhs (deleted)
      (send c (hash current-value value)) ;; MSR rhs
      (send "ext ok"))
     (conf c)
     (auth c))

   ;; The extend command can also occur within an
   ;; encrypted session.  We assume some session key already exists
   (defrole tpm-extend-enc
     (vars (value current-value mesg) (esk skey) (c chan))
     (trace
      (recv (enc "extend" value esk))
      (recv c current-value)		  ;; MSR lhs (deleted)
      (send c (hash current-value value)) ;; MSR rhs
      (send "ext ok"))
     (non-orig esk)
     (conf c)
     (auth c))

   ;; The TPM must retrieve the current pcr value.  Notice that
   ;; the nonce is of sort mesg, which allows non-atomic values.
   (defrole tpm-quote
     (vars (nonce current-value mesg) (c chan) (aik akey))
     (trace
      (recv (cat "quote" nonce))
      (recv c current-value) ;; MSR lhs (not deleted)
      (send (enc "quote" current-value nonce aik)))
     (non-orig aik)
     (conf c)
     (auth c))

   ;; This role creates a key whose use is restricted to a
   ;; requested pcr value (since we only model one pcr).
   ;; It doesn't create or change any TPM state.
   (defrole tpm-create-key
     (vars (k aik akey) (pcrval mesg) (esk skey))
     (trace
      (recv (enc "create key" pcrval esk)) ;; encryption prevents weird shapes
      (send (enc "created" k pcrval aik)));; no tpm state is set
     (uniq-orig k)
     (non-orig (invk k) aik esk))

   ;; This role receives an encryption and a previously
   ;; made key structure that restricts the decryption key
   ;; to be used with a certain pcr value.  It retrieves the
   ;; current value and checks that it matches before decrypting.
   (defrole tpm-decrypt
     (vars (m pcrvals mesg) (k aik akey) (c chan))
     (trace
      (recv (cat "decrypt" (enc m k)))
      (recv (enc "created" k pcrvals aik))
      (recv c pcrvals) ;; MSR lhs (not deleted)
      (send m))
     (non-orig aik)
     (conf c)
     (auth c))

   ;; Alice extends a pcr with a fresh nonce in an encrypted
   ;; session.  She has the TPM create a new key whose use is
   ;; bound to the hash of pcr value she just created with the
   ;; string "obtain".  She then encrypts her fresh secret with
   ;; this newly created key.
   (defrole alice
     (vars (n v data) (esk skey) (k aik akey))
     (trace
      (send (enc "extend" n esk))
      (send (enc "create key" (hash (hash "0" n) "obtain") esk))
      (recv (enc "created" k (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
     (uniq-orig n v)
     (non-orig aik esk))))

(defprotocol envelope basic
  (roles))

(defskeleton envelope
  (vars (v data))
  (deflistener v)
  (defstrand alice 4 (v v)))

(defskeleton envelope
  (vars (n v data) (k aik akey))
  (deflistener (refuse n v k aik))
  (defstrand alice 4 (n n) (v v) (k k) (aik aik)))

(defskeleton envelope
  (vars (n v data) (k aik akey))
  (deflistener (refuse n v k aik))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (k k) (aik aik)))

(defprotocol envelope basic
  (roles)

  (defrule ordered-extends
    (forall ((y z strd) (c chan))
	    (implies
	     (and (p "tpm-extend" y 3)
		  (p "tpm-extend" z 3)
		  (p "tpm-extend" "c" y c)
		  (p "tpm-extend" "c" z c))
	     (or (= y z)
		 (prec y 2 z 3)
		 (prec z 2 y 3))))))

(defskeleton envelope
  (vars (v data))
  (deflistener v)
  (defstrand alice 4 (v v)))

(defskeleton envelope
  (vars (n v data) (k aik akey))
  (deflistener (refuse n v k aik))
  (defstrand alice 4 (n n) (v v) (k k) (aik aik)))

(defskeleton envelope
  (vars (n v data) (k aik akey))
  (deflistener (refuse n v k aik))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (k k) (aik aik)))

(defprotocol envelope basic
  (roles)

  (defrule ordered-extends
    (forall ((y z strd) (c chan))
	    (implies
	     (and (p "tpm-extend" y 3)
		  (p "tpm-extend" z 3)
		  (p "tpm-extend" "c" y c)
		  (p "tpm-extend" "c" z c))
	     (or (= y z)
		 (prec y 2 z 3)
		 (prec z 2 y 3)))))

  (defrule esk-same-as-chan
    (forall ((y z strd) (esk skey) (c c-0 chan))
	    (implies
	     (and (p "tpm-extend-enc" y 3)
		  (p "tpm-extend-enc" z 3)
		  (p "tpm-extend-enc" "esk" y esk)
		  (p "tpm-extend-enc" "esk" z esk)
		  (p "tpm-extend-enc" "c" y c)
		  (p "tpm-extend-enc" "c" z c-0))
	     (= c c-0)))))

(defskeleton envelope
  (vars (v data))
  (deflistener v)
  (defstrand alice 4 (v v)))

(defskeleton envelope
  (vars (n v data) (k aik akey))
  (deflistener (refuse n v k aik))
  (defstrand alice 4 (n n) (v v) (k k) (aik aik)))

(defskeleton envelope
  (vars (n v data) (k aik akey))
  (deflistener (refuse n v k aik))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (k k) (aik aik)))
