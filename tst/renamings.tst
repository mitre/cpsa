(herald "Blanchet's Simple Example Protocol"
  (comment "There is a flaw in this protocol by design")
  (comment "It also shows how variable renaming works"))

(comment "CPSA 4.2.3")
(comment "All input read from tst/renamings.scm")

(defprotocol blanchet basic
  (defrole init
    (vars (a b name) (s skey) (d data))
    (trace (send (enc (enc s (privk a)) (pubk b))) (recv (enc d s))))
  (defrole resp
    (vars (d a name) (b skey) (s data))
    (trace (recv (enc (enc b (privk d)) (pubk a))) (send (enc s b))))
  (comment "Blanchet's protocol using named asymmetric keys"))

(defskeleton blanchet
  (vars (b data) (s d name) (a skey))
  (defstrand resp 2 (s b) (d s) (a d) (b a))
  (non-orig (privk s) (privk d))
  (uniq-orig a)
  (comment "Analyze from the responder's perspective")
  (traces ((recv (enc (enc a (privk s)) (pubk d))) (send (enc b a))))
  (label 0)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet
  (vars (b data) (s d b-0 name) (a skey))
  (defstrand resp 2 (s b) (d s) (a d) (b a))
  (defstrand init 1 (a s) (b b-0) (s a))
  (precedes ((1 0) (0 0)))
  (non-orig (privk s) (privk d))
  (uniq-orig a)
  (operation encryption-test (added-strand init 1) (enc a (privk s))
    (0 0))
  (traces ((recv (enc (enc a (privk s)) (pubk d))) (send (enc b a)))
    ((send (enc (enc a (privk s)) (pubk b-0)))))
  (label 1)
  (parent 0)
  (unrealized)
  (shape)
  (maps ((0) ((s s) (d d) (a a) (b b))))
  (origs (a (1 0))))

(comment "Nothing left to do")

(defprotocol blanchet basic
  (defrole init
    (vars (a b name) (s skey) (d data))
    (trace (send (enc (enc s (privk a)) (pubk b))) (recv (enc d s))))
  (defrole resp
    (vars (d a name) (b skey) (s data))
    (trace (recv (enc (enc b (privk d)) (pubk a))) (send (enc s b))))
  (comment "Blanchet's protocol using named asymmetric keys"))

(defskeleton blanchet
  (vars (b data) (s d name) (a skey))
  (defstrand init 2 (d b) (a s) (b d) (s a))
  (non-orig (privk d))
  (uniq-orig a)
  (comment "Analyze from the initiator's perspective")
  (traces ((send (enc (enc a (privk s)) (pubk d))) (recv (enc b a))))
  (label 2)
  (unrealized (0 1))
  (origs (a (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton blanchet
  (vars (b data) (s d d-0 a name) (a-0 skey))
  (defstrand init 2 (d b) (a s) (b d) (s a-0))
  (defstrand resp 2 (s b) (d d-0) (a a) (b a-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk d))
  (uniq-orig a-0)
  (operation encryption-test (added-strand resp 2) (enc b a-0) (0 1))
  (traces ((send (enc (enc a-0 (privk s)) (pubk d))) (recv (enc b a-0)))
    ((recv (enc (enc a-0 (privk d-0)) (pubk a))) (send (enc b a-0))))
  (label 3)
  (parent 2)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet
  (vars (b data) (s d name) (a skey))
  (defstrand init 2 (d b) (a s) (b d) (s a))
  (deflistener a)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk d))
  (uniq-orig a)
  (operation encryption-test (added-listener a) (enc b a) (0 1))
  (traces ((send (enc (enc a (privk s)) (pubk d))) (recv (enc b a)))
    ((recv a) (send a)))
  (label 4)
  (parent 2)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton blanchet
  (vars (b data) (s d name) (a skey))
  (defstrand init 2 (d b) (a s) (b d) (s a))
  (defstrand resp 2 (s b) (d s) (a d) (b a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk d))
  (uniq-orig a)
  (operation nonce-test (contracted (d-0 s) (a-0 d)) a (1 0)
    (enc (enc a (privk s)) (pubk d)))
  (traces ((send (enc (enc a (privk s)) (pubk d))) (recv (enc b a)))
    ((recv (enc (enc a (privk s)) (pubk d))) (send (enc b a))))
  (label 5)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0) ((s s) (d d) (a a) (b b))))
  (origs (a (0 0))))

(comment "Nothing left to do")
