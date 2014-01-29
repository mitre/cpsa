;; This is to test the pen-non-orig declaration.
;; The password, pwd, should not be known to the
;; penetrator at the outset.  Thus, even over an
;; unencrypted channel, the server should infer
;; a good client.  However, the password is
;; learned in the process, hence the skeleton
;; with a listener will also be realized.

(herald "pen-non-orig test")

(defprotocol pennonorigtest basic
  (defrole client
    (vars (userid name) (pwd text))
    (trace
     (send (cat userid pwd))))
  (defrole server
    (vars (userid name) (pwd text))
    (trace
     (recv (cat userid pwd)))
    (pen-non-orig pwd)))

(defskeleton pennonorigtest
  (vars (pwd text))
  (defstrand server 1 (pwd pwd)))

(defskeleton pennonorigtest
  (vars (pwd text))
  (defstrand server 1 (pwd pwd))
  (deflistener pwd))
