(herald "pen-non-orig test")

(comment "CPSA 2.3.1")
(comment "All input read from pen-non-orig-test.scm")

(defprotocol pennonorigtest basic
  (defrole client
    (vars (userid name) (pwd text))
    (trace (send (cat userid pwd))))
  (defrole server
    (vars (userid name) (pwd text))
    (trace (recv (cat userid pwd)))
    (pen-non-orig pwd)))

(defskeleton pennonorigtest
  (vars (pwd text) (userid name))
  (defstrand server 1 (pwd pwd) (userid userid))
  (pen-non-orig pwd)
  (traces ((recv (cat userid pwd))))
  (label 0)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pennonorigtest
  (vars (pwd text) (userid userid-0 name))
  (defstrand server 1 (pwd pwd) (userid userid))
  (defstrand client 1 (pwd pwd) (userid userid-0))
  (precedes ((1 0) (0 0)))
  (pen-non-orig pwd)
  (operation nonce-test (added-strand client 1) pwd (0 0))
  (traces ((recv (cat userid pwd))) ((send (cat userid-0 pwd))))
  (label 1)
  (parent 0)
  (unrealized)
  (shape)
  (maps ((0) ((pwd pwd) (userid userid))))
  (origs))

(comment "Nothing left to do")

(defprotocol pennonorigtest basic
  (defrole client
    (vars (userid name) (pwd text))
    (trace (send (cat userid pwd))))
  (defrole server
    (vars (userid name) (pwd text))
    (trace (recv (cat userid pwd)))
    (pen-non-orig pwd)))

(defskeleton pennonorigtest
  (vars (pwd text) (userid name))
  (defstrand server 1 (pwd pwd) (userid userid))
  (deflistener pwd)
  (pen-non-orig pwd)
  (traces ((recv (cat userid pwd))) ((recv pwd) (send pwd)))
  (label 2)
  (unrealized (0 0) (1 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pennonorigtest
  (vars (pwd text) (userid userid-0 name))
  (defstrand server 1 (pwd pwd) (userid userid))
  (deflistener pwd)
  (defstrand client 1 (pwd pwd) (userid userid-0))
  (precedes ((2 0) (1 0)))
  (pen-non-orig pwd)
  (operation nonce-test (added-strand client 1) pwd (1 0))
  (traces ((recv (cat userid pwd))) ((recv pwd) (send pwd))
    ((send (cat userid-0 pwd))))
  (label 3)
  (parent 2)
  (unrealized (0 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton pennonorigtest
  (vars (pwd text) (userid userid-0 name))
  (defstrand server 1 (pwd pwd) (userid userid))
  (deflistener pwd)
  (defstrand client 1 (pwd pwd) (userid userid-0))
  (precedes ((2 0) (0 0)) ((2 0) (1 0)))
  (pen-non-orig pwd)
  (operation nonce-test (displaced 3 2 client 1) pwd (0 0))
  (traces ((recv (cat userid pwd))) ((recv pwd) (send pwd))
    ((send (cat userid-0 pwd))))
  (label 4)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0 1) ((pwd pwd) (userid userid))))
  (origs))

(defskeleton pennonorigtest
  (vars (pwd text) (userid userid-0 userid-1 name))
  (defstrand server 1 (pwd pwd) (userid userid))
  (deflistener pwd)
  (defstrand client 1 (pwd pwd) (userid userid-0))
  (defstrand client 1 (pwd pwd) (userid userid-1))
  (precedes ((2 0) (1 0)) ((3 0) (0 0)))
  (pen-non-orig pwd)
  (operation nonce-test (added-strand client 1) pwd (0 0))
  (traces ((recv (cat userid pwd))) ((recv pwd) (send pwd))
    ((send (cat userid-0 pwd))) ((send (cat userid-1 pwd))))
  (label 5)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0 1) ((pwd pwd) (userid userid))))
  (origs))

(comment "Nothing left to do")
