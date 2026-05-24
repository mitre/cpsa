(herald "Dev and Locn" 
  (comment "This tests the feature that allows loads and stors to have any message in their location position."))

(defprotocol devlocn basic
  (defrole init
    (vars (d dev) (l1 l2 locn) (n1 n2 data) (k skey))
    (trace
     (stor (cat d l1) n1)
     (stor (cat d l2) n2)
     (send (enc d l1 k))
     (send (enc d l2 k)))
    (uniq-orig n1 n2 d))
  (defrole resp
    (vars (d dev) (l locn) (m mesg) (k skey))
    (trace
     (recv (enc d l k))
     (load (cat d l) m)
     (send m))
    (non-orig k))) 

(defskeleton devlocn
  (vars (n1 n2 data))
  (defstrand init 2 (n1 n1) (n2 n2))
  (deflistener n1)
  (deflistener n2))

(defprotocol devlocn basic
  (defrole init
    (vars (d dev) (l1 l2 locn) (n1 n2 data) (k skey))
    (trace
     (stor (cat d l1) n1)
     (send (enc d l1 k)))
    (uniq-orig n1 l1))
  (defrole resp
    (vars (d dev) (l locn) (m mesg) (k skey))
    (trace
     (recv (enc d l k))
     (load (cat d l) m)
     (send m))
    (non-orig k))) 

(defskeleton devlocn
  (vars (n1 n2 data))
  (defstrand init 1 (n1 n1))
  (defstrand init 1 (n1 n2))
  (deflistener n1)
  (deflistener n2))

(defskeleton devlocn
  (vars (n1 n2 data) (d1 d2 dev))
  (defstrand init 1 (n1 n1) (d d1))
  (defstrand init 1 (n1 n2) (d d2))
  (deflistener n1)
  (deflistener n2)
  (facts (neq d1 d2))
  (comment "With different devices they cannot have the same source."))

(defskeleton devlocn
  (vars (n1 n2 data) (l1 l2 locn))
  (defstrand init 1 (n1 n1) (l1 l1))
  (defstrand init 1 (n1 n2) (l1 l2))
  (deflistener n1)
  (deflistener n2)
  (facts (neq l1 l2))
  (comment "With different locns they cannot have the same source."))

(defskeleton devlocn
  (vars (n1 n2 data) (l1 l2 locn) (d dev))
  (defstrand init 1 (n1 n1) (l1 l1) (d d))
  (defstrand init 1 (n1 n2) (l1 l2) (d d))
  (deflistener n1)
  (deflistener n2)
  (facts (neq l1 l2))
  (comment "With different locns they cannot have the same source even if the devs are the same."))


(defprotocol devlocn basic
  (defrole init
    (vars (d dev) (l1 l2 locn) (n1 n2 data) (k skey))
    (trace
     (stor (cat d l1) n1)
     (send (enc d l1 k)))
    (uniq-orig n1 l1))
  (defrole resp
    (vars (d dev) (l locn) (dl m mesg) (k skey))
    (trace
     (recv (enc dl k))
     (load dl m)
     (send m)
     )
    (non-orig k))
  (comment "Notice the mesg var dl as location for load. Only allowed because it is acquired."))

(defskeleton devlocn
  (vars (m mesg))
  (defstrand resp 2 (m m))
  (gen-st m))

(defskeleton devlocn
  (vars (m mesg))
  (defstrand resp 2 (m m))
  (comment "Possibly strange interpretation. Init has uniq-orig n1 and l1. Resp doesn't necessarily retrieve n1, even though nobody but Init should know l1, so nobody else could stor into it."))

(defskeleton devlocn
  (vars (n data))
  (defstrand resp 2 (m n))
  (defstrand init 2 (n1 n))
  (comment "Even if loaded value is not gen-st, since it's uniq-orig, nonce-test still applies."))
