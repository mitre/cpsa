(herald "Privacy Certificate Authority" (bound 15)
  (comment "Generation of an Attestation Identity Certificate"))

;;; PCA generation of AIC, simplified

;;; ki = identity key
;;; a = identity label
;;; t = TPM type/platform
;;; ke = endorsement key
;;; kp = PCA key
;;; km = manufacturer key
;;; (enc (cat ki a t) (invk kp)) is the signed AIC

(defprotocol pca basic
  (defrole tpm (vars (ke ki km kp akey) (t a text))
    (trace
     (send (cat (enc ki a (invk ki)) (enc t ke (invk km))))
     (recv (enc (enc ki a t (invk kp)) ke))
     (send (enc ki a t (invk kp))))
    (non-orig (invk ke) (invk ki) (invk km) (invk kp))
    (uniq-orig ki))
  (defrole pca (vars (ke ki km kp akey) (t a text))
    (trace
     (recv (cat (enc ki a (invk ki)) (enc t ke (invk km))))
     (send (enc (enc ki a t (invk kp)) ke)))
    (non-orig (invk ke) (invk ki) (invk km) (invk kp)))
  (defrole appr (vars (ki kp akey) (t a text))
    (trace
     (recv (enc ki a t (invk kp))))
    (non-orig (invk ki) (invk kp))))

;;; normal run

(defskeleton pca (vars (ki kp akey))
  (defstrand appr 1 (ki ki) (kp kp))
  (non-orig (invk ki) (invk kp)))
