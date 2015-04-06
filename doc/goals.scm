(herald goals)

;;; Section 1 --- Examples from CPSA and Formal Security Goals

;;; Needham-Schroeder from Section 10 of the CPSA Primer

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace
     (send (enc n1 a (pubk b)))
     (recv (enc n1 n2 (pubk a)))
     (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace
     (recv (enc n1 a (pubk b)))
     (send (enc n1 n2 (pubk a)))
     (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder with no role origination assumptions"))

;;; The initiator point of view
(defskeleton ns
  (vars (a b name) (n1 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (non-orig (privk b) (privk a))
  (uniq-orig n1)
  (goals
   (forall ((n1 n2 text) (a b name) (z z-0 node))
    (implies
      (and (p "init" 0 z) (p "init" 2 z-0)
        (p "init" "n1" z-0 n1) (p "init" "n2" z-0 n2)
        (p "init" "a" z-0 a) (p "init" "b" z-0 b)
        (str-prec z z-0) (non (privk a)) (non (privk b))
        (uniq-at n1 z))
      (exists ((z-1 z-2 z-3 node))
        (and (p "init" 1 z-1) (p "resp" 0 z-2)
          (p "resp" 1 z-3) (p "resp" "n2" z-3 n2)
          (p "resp" "n1" z-3 n1) (p "resp" "b" z-3 b)
          (p "resp" "a" z-3 a) (prec z z-2) (prec z-3 z-1)
          (str-prec z z-1) (str-prec z-1 z-0)
          (str-prec z-2 z-3))))))
  (comment "Initiator point of view"))

(defskeleton ns
  (vars (a name) (n2 text))
  (defstrand resp 3 (a a) (n2 n2))
  (non-orig (privk a))
  (uniq-orig n2)
  (goals
   (forall ((n1 n2 text) (a b name) (z z-0 node))
    (implies
      (and (p "init" 0 z) (p "init" 2 z-0)
        (p "init" "n1" z-0 n1) (p "init" "n2" z-0 n2)
        (p "init" "a" z-0 a) (p "init" "b" z-0 b)
        (str-prec z z-0) (non (privk a)) (non (privk b))
        (uniq-at n1 z))
      (exists ((z-1 z-2 z-3 node))
        (and (p "init" 1 z-1) (p "resp" 0 z-2)
          (p "resp" 1 z-3) (p "resp" "n2" z-3 n2)
          (p "resp" "n1" z-3 n1) (p "resp" "b" z-3 b)
          (p "resp" "a" z-3 a) (prec z z-2) (prec z-3 z-1)
          (str-prec z z-1) (str-prec z-1 z-0)
          (str-prec z-2 z-3))))))
  (comment "Responder point of view"))

(defskeleton ns
  (vars (a name) (n2 text))
  (defstrand resp 3 (a a) (n2 n2))
  (non-orig (privk a))
  (uniq-orig n2)
  (goals
   (forall ((n1 n2 text) (a b name) (z z-0 node))
    (implies
      (and (p "init" 0 z) (p "init" 2 z-0)
        (p "init" "n1" z-0 n1) (p "init" "n2" z-0 n2)
        (p "init" "a" z-0 a) (p "init" "b" z-0 b)
        (str-prec z z-0) (non (privk a)) (non (privk b))
        (uniq-at n1 z))
      (false))))
  (comment "Responder point of view with false as the conclusion"))

(defskeleton ns
  (vars (a b name) (n1 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (non-orig (privk b) (privk a))
  (uniq-orig n1)
  (goals
   (forall ((n1 n2 text) (a b name) (z z-0 node))
    (implies
      (and (p "init" 0 z) (p "init" 2 z-0)
        (p "init" "n1" z-0 n1) (p "init" "n2" z-0 n2)
        (p "init" "a" z-0 a) (p "init" "b" z-0 b)
        (str-prec z z-0) (non (privk a)) (non (privk b))
        (uniq-at n1 z))
      (false))))
  (comment "Initiator point of view with false as the conclusion"))

(defgoal ns
  (forall ((a b name) (n text) (z0 node))
    (implies
     (and 
      (p "init" 1 z0) (p "init" "n1" z0 n)
      (p "init" "a" z0 a) (p "init" "b" z0 b)
      (non (privk a)) (non (privk b)) (uniq n))
     (exists ((z1 node))
      (and (p "resp" 1 z1) (p "resp" "b" z1 b)))))
  (forall ((a b name) (n text) (z0 node))
   (implies
     (and 
      (p "init" 1 z0) (p "init" "n1" z0 n)
      (p "init" "a" z0 a) (p "init" "b" z0 b)
      (non (privk a)) (non (privk b)) (uniq n))
     (exists ((z1 node))
      (and (p "resp" 1 z1) (p "resp" "a" z1 a)))))
  (comment "Two initiator authentication goals"))

(defgoal ns
  (forall ((a b name) (n text) (z0 node))
   (implies
    (and 
     (p "resp" 2 z0) (p "resp" "n2" z0 n)
     (p "resp" "a" z0 a) (p "resp" "b" z0 b)
     (non (privk a)) (non (privk b)) (uniq n))
    (exists ((z1 node))
     (and (p "init" 2 z1) (p "init" "a" z1 a)))))
  (forall ((a b name) (n text) (z0 node))
   (implies
    (and 
     (p "resp" 2 z0) (p "resp" "n2" z0 n)
     (p "resp" "a" z0 a) (p "resp" "b" z0 b)
     (non (privk a)) (non (privk b)) (uniq n))
    (exists ((z1 node))
     (and (p "init" 2 z1) (p "init" "b" z1 b)))))
  (comment "Two responder authentication goals"))

(defprotocol unilateral basic
  (defrole init
     (vars (a name) (n text))
     (trace
      (send (enc n (pubk a)))
      (recv n)))
  (defrole resp
     (vars (a name) (n text))
     (trace
      (recv (enc n (pubk a)))
      (send n))))

(defgoal unilateral
  (forall ((a name) (n text)
           (z0 node))
   (implies
    (and (p "init" 1 z0)
     (p "init" "n" z0 n)
     (p "init" "a" z0 a)
     (non (privk a)) (uniq n))
    (exists ((z1 node))
     (and (p "resp" 1 z1) 
      (p "resp" "a" z1 a))))))

;;; Does initiator satisfy the unilateral authentication goal?

;;; Note that the goal requires translation of some of the role
;;; specific predicates.
(defgoal ns
  (forall ((a name) (n text) (z0 node))
   (implies
    (and (p "init" 1 z0) (p "init" "n1" z0 n)
     (p "init" "b" z0 a) (non (privk a)) (uniq n))
    (exists ((z1 node))
     (and (p "resp" 1 z1) (p "resp" "b" z1 a)))))
  (comment "Initiator authentication goal")
  (comment "Same as unilateral goal under the predicate mapping:")
  (comment (p "init" "n") "->" (p "init" "n1") "and")
  (comment (p "init" "a") "->" (p "init" "b") "and")
  (comment (p "resp" "a") "->" (p "resp" "b")))
  
;;; Does responder satisfy the unilateral authentication goal?

(defgoal ns
  (forall ((a name) (n text) (z0 node))
   (implies
    (and (p "resp" 2 z0) (p "resp" "n2" z0 n)
     (p "resp" "a" z0 a) (non (privk a)) (uniq n))
    (exists ((z1 node))
     (and (p "init" 2 z1) (p "init" "a" z1 a)))))
  (comment "Responder authentication goal")
  (comment "Same as unilateral goal under the predicate mapping:")
  (comment (p "init" 1) "->" (p "resp" 2) "and")
  (comment (p "init" "n") "->" (p "resp" "n2") "and")
  (comment (p "init" "a") "->" (p "resp" "a") "and")
  (comment (p "resp" 1) "->" (p "init" 2) "and")
  (comment (p "resp" "a") "->" (p "init" "a")))

;;; Section 2 --- Additional Examples

;;; The shape analysis sentence as input (kind of useless)

(defgoal ns                ; Shape analysis sentence
  (forall ((n1 n2 text) (a b name) (z z-0 node))
    (implies
      (and (p "init" 0 z) (p "init" 2 z-0)
        (p "init" "n1" z-0 n1) (p "init" "n2" z-0 n2)
        (p "init" "a" z-0 a) (p "init" "b" z-0 b)
        (str-prec z z-0) (non (privk a)) (non (privk b))
        (uniq-at n1 z))
      (exists ((z-1 z-2 z-3 node))
        (and (p "init" 1 z-1) (p "resp" 0 z-2)
          (p "resp" 1 z-3) (p "resp" "n2" z-3 n2)
          (p "resp" "n1" z-3 n1) (p "resp" "b" z-3 b)
          (p "resp" "a" z-3 a) (prec z z-2) (prec z-3 z-1)
          (str-prec z z-1) (str-prec z-1 z-0)
          (str-prec z-2 z-3)))))
  (comment "Shape analysis sentence"))

(defskeleton ns
  (vars (a b name) (n1 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (non-orig (privk b) (privk a))
  (uniq-orig n1)
  (goals
   (forall ((a b name) (n1 text) (no nu node))
           (implies
            (and (p "init" 2 no)
                 (p "init" "a" no a)
                 (p "init" "b" no b)
                 (p "init" "n1" no n1)
                 (p "init" 0 nu)
                 (str-prec nu no)
                 (non (privk a))
                 (non (privk b))
                 (uniq-at n1 nu))
            (exists ((na nb node))
                    (and (p "init" 2 na)
                         (p "resp" 1 nb)
                         (p "init" "b" na b)
                         (p "resp" "b" nb b))))))
  (comment "Initiator point of view"))

(defgoal ns
  (forall ((a b name) (n1 text) (no nu node))
          (implies
           (and (p "init" 2 no)
                (p "init" "a" no a)
                (p "init" "b" no b)
                (p "init" "n1" no n1)
                (p "init" 0 nu)
                (str-prec nu no)
                (non (privk a))
                (non (privk b))
                (uniq-at n1 nu))
           (exists ((na nb node))
                   (and (p "init" 2 na)
                        (p "resp" 1 nb)
                        (p "init" "b" na b)
                        (p "resp" "b" nb b)))))
  (comment "Initiator point of view"))

;;; The responder point of view
(defskeleton ns
  (vars (a name) (n2 text))
  (defstrand resp 3 (a a) (n2 n2))
  (non-orig (privk a))
  (uniq-orig n2)
  (goals
  (forall ((n2 n1 text) (a b name) (z z-0 node))
    (implies
      (and (p "resp" 1 z) (p "resp" 2 z-0) (p "resp" "n2" z-0 n2)
        (p "resp" "n1" z-0 n1) (p "resp" "b" z-0 b) (p "resp" "a" z-0 a)
        (str-prec z z-0) (non (privk a)) (uniq-at n2 z))
      (exists ((b-0 name) (z-1 z-2 node))
        (and (p "init" 1 z-1) (p "init" 2 z-2) (p "init" "n1" z-2 n1)
          (p "init" "n2" z-2 n2) (p "init" "a" z-2 a)
          (p "init" "b" z-2 b-0) (prec z z-1) (prec z-2 z-0)
          (str-prec z-1 z-2))))))
  (comment "Responder point of view"))

;;; The responder point of view
(defskeleton ns
  (vars (a name) (n2 text))
  (defstrand resp 3 (a a) (n2 n2))
  (non-orig (privk a))
  (uniq-orig n2)
  (goals
   (forall ((n2 n1 text) (a b name) (z z-0 node))
    (implies
      (and (p "resp" 1 z) (p "resp" 2 z-0) (p "resp" "n2" z-0 n2)
        (p "resp" "n1" z-0 n1) (p "resp" "b" z-0 b) (p "resp" "a" z-0 a)
        (str-prec z z-0) (non (privk a)) (uniq-at n2 z))
      (exists ((b-0 name) (z-1 z-2 node))
        (and (p "init" 1 z-1) (p "init" 2 z-2) (p "init" "n1" z-2 n1)
          (p "init" "n2" z-2 n2) (p "init" "a" z-2 a)
          (p "init" "b" z-2 b-0) (prec z z-1) (prec z-2 z-0)
          (str-prec z-1 z-2))))))
  (comment "Responder point of view"))

;;; Double initiator point of view
(defskeleton ns
  (vars (a b name) (n1 n1-0 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (defstrand init 3 (a a) (b b) (n1 n1-0))
  (non-orig (privk b) (privk a))
  (uniq-orig n1 n1-0)
  (goals
   (forall ((n1 n1-0 n2 n2-0 text) (a b name) (z z-0 z-1 z-2 node))
           (implies
            (and (p "init" 0 z) (p "init" 2 z-0) (p "init" 0 z-1)
                 (p "init" 2 z-2) (p "init" "n1" z-0 n1) (p "init" "n2" z-0 n2)
                 (p "init" "a" z-0 a) (p "init" "b" z-0 b)
                 (p "init" "n1" z-2 n1-0) (p "init" "n2" z-2 n2-0)
                 (p "init" "a" z-2 a) (p "init" "b" z-2 b) (str-prec z z-0)
                 (str-prec z-1 z-2) (non (privk a)) (non (privk b))
                 (uniq-at n1 z) (uniq-at n1-0 z-1))
            (= z-1 z))))
  (comment "Double initiator point of view"))

;;; Needham-Schroeder Protocol with origination assumptions on roles
;;; This

(defprotocol ns-role-origs basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace
     (send (enc n1 a (pubk b)))
     (recv (enc n1 n2 (pubk a)))
     (send (enc n2 (pubk b))))
    (non-orig (privk b))
    (uniq-orig n1))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace
     (recv (enc n1 a (pubk b)))
     (send (enc n1 n2 (pubk a)))
     (recv (enc n2 (pubk b))))
    (non-orig (privk a))
    (uniq-orig n2))
  (comment "Needham-Schroeder with role assumptions that are too strong"))

;;; The initiator point of view
(defskeleton ns-role-origs
  (vars)
  (defstrand init 3))

;;; The responder point of view
(defskeleton ns-role-origs
  (vars)
  (defstrand resp 3))

;;; Needham-Schroeder Protocol with a doubled nonce.  Look at the
;;; first message in each role.

(defprotocol ns2 basic
  (defrole init
    (vars (a b name) (n1 n2 n3 text))
    (trace
     (send (enc n1 n3 a (pubk b)))
     (recv (enc n1 n2 (pubk a)))
     (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace
     (recv (enc n1 n1 a (pubk b)))
     (send (enc n1 n2 (pubk a)))
     (recv (enc n2 (pubk b))))
    (note doubled nonce in the first message))
  (note that this protocol is derived from Needham-Schroeder))

(defskeleton ns2
  (vars (a b name) (n1 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (non-orig (privk b) (privk a))
  (uniq-orig n1)
  (note the disappearance of this note))

;;; Note that the association list style key-value pairs that follow
;;; the list of strands can be supplied in any order, and values with
;;; the same key are appended together.  Check the output to see how
;;; CPSA interprets this input.
(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1) (b b) (a a))
  (non-orig (privk b))
  (precedes ((0 0) (1 0)))
  (non-orig (privk a))
  (uniq-orig n1)
  (precedes ((1 1) (0 1))))

(defprotocol nsl-typeless basic
  (defrole init
    (vars (a b name) (n1 text) (n2 mesg))
    (trace
     (send (enc a n1 (pubk b)))
     (recv (enc n1 n2 b (pubk a)))
     (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 text) (n1 mesg))
    (trace
     (recv (enc a n1 (pubk b)))
     (send (enc n1 n2 b (pubk a)))
     (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder-Lowe with untyped nonces"))

;;; The responder point of view
(defskeleton nsl-typeless
  (vars (a b name) (n2 text))
  (defstrand resp 2 (a a) (n2 n2) (b b))
  (deflistener n2)
  (non-orig (privk a) (privk b))
  (uniq-orig n2)
  (comment "Shows typeflaw in typeless NSL"))
