(herald yes-or-no)

(defprotocol yes-or-no basic
  (defrole init-positive
    (vars (y n data) (question text) (ans name) (ans-key akey))
    (trace
     (send (enc question y n ans-key))
     (recv y)))

  (defrole init-negative
    (vars (y n data) (question text) (ans name) (ans-key akey))
    (trace
     (send (enc question y n ans-key))
     (recv n)))

  (defrole resp-positive
    (vars (y n data) (question text) (ans name) (ans-key akey))
    (trace
     (recv (enc question y n ans-key))
     (send y)))

  (defrole resp-negative
    (vars (y n data) (question text) (ans name) (ans-key akey))
    (trace
     (recv (enc question y n ans-key))
     (send n))))

(defskeleton yes-or-no
  (vars (y data) (ans-key akey))
  (defstrand init-positive 2 (y y) (ans-key ans-key))
  (uniq-orig y)
  (non-orig (invk ans-key)))

(defskeleton yes-or-no
  (vars (ans-key akey) (n data))
  (defstrand init-negative 2 (n n) (ans-key ans-key))
  (uniq-orig n) 
  (non-orig (invk ans-key)))

(defskeleton yes-or-no
  (vars (y data) (ans-key akey))
  (defstrand init-positive 1 (y y) (ans-key ans-key))
  (deflistener y)
  (uniq-orig y)
  (non-orig (invk ans-key)))

(defskeleton yes-or-no
  (vars (n data) (ans-key akey))
  (defstrand init-positive 1 (n n) (ans-key ans-key))
  (deflistener n) 
  (uniq-orig n)
  (non-orig (invk ans-key)))
