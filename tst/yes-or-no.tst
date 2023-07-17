(herald yes-or-no)

(comment "CPSA 4.4.2")
(comment "All input read from yes-or-no.scm")

(defprotocol yes-or-no basic
  (defrole init-positive
    (vars (y n data) (question text) (ans-key akey))
    (trace (send (enc question y n ans-key)) (recv y)))
  (defrole init-negative
    (vars (y n data) (question text) (ans-key akey))
    (trace (send (enc question y n ans-key)) (recv n)))
  (defrole resp-positive
    (vars (y n data) (question text) (ans-key akey))
    (trace (recv (enc question y n ans-key)) (send y)))
  (defrole resp-negative
    (vars (y n data) (question text) (ans-key akey))
    (trace (recv (enc question y n ans-key)) (send n)))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton yes-or-no
  (vars (y n data) (question text) (ans-key akey))
  (defstrand init-positive 2 (y y) (n n) (question question)
    (ans-key ans-key))
  (non-orig (invk ans-key))
  (uniq-orig y)
  (traces ((send (enc question y n ans-key)) (recv y)))
  (label 0)
  (unrealized (0 1))
  (origs (y (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton yes-or-no
  (vars (y n data) (question text) (ans-key akey))
  (defstrand init-positive 2 (y y) (n n) (question question)
    (ans-key ans-key))
  (defstrand resp-positive 2 (y y) (n n) (question question)
    (ans-key ans-key))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk ans-key))
  (uniq-orig y)
  (operation nonce-test (added-strand resp-positive 2) y (0 1)
    (enc question y n ans-key))
  (traces ((send (enc question y n ans-key)) (recv y))
    ((recv (enc question y n ans-key)) (send y)))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((y y) (ans-key ans-key) (n n) (question question))))
  (origs (y (0 0))))

(comment "Nothing left to do")

(defprotocol yes-or-no basic
  (defrole init-positive
    (vars (y n data) (question text) (ans-key akey))
    (trace (send (enc question y n ans-key)) (recv y)))
  (defrole init-negative
    (vars (y n data) (question text) (ans-key akey))
    (trace (send (enc question y n ans-key)) (recv n)))
  (defrole resp-positive
    (vars (y n data) (question text) (ans-key akey))
    (trace (recv (enc question y n ans-key)) (send y)))
  (defrole resp-negative
    (vars (y n data) (question text) (ans-key akey))
    (trace (recv (enc question y n ans-key)) (send n)))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton yes-or-no
  (vars (n y data) (question text) (ans-key akey))
  (defstrand init-negative 2 (y y) (n n) (question question)
    (ans-key ans-key))
  (non-orig (invk ans-key))
  (uniq-orig n)
  (traces ((send (enc question y n ans-key)) (recv n)))
  (label 2)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton yes-or-no
  (vars (n y data) (question text) (ans-key akey))
  (defstrand init-negative 2 (y y) (n n) (question question)
    (ans-key ans-key))
  (defstrand resp-negative 2 (y y) (n n) (question question)
    (ans-key ans-key))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk ans-key))
  (uniq-orig n)
  (operation nonce-test (added-strand resp-negative 2) n (0 1)
    (enc question y n ans-key))
  (traces ((send (enc question y n ans-key)) (recv n))
    ((recv (enc question y n ans-key)) (send n)))
  (label 3)
  (parent 2)
  (realized)
  (shape)
  (maps ((0) ((ans-key ans-key) (n n) (y y) (question question))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol yes-or-no basic
  (defrole init-positive
    (vars (y n data) (question text) (ans-key akey))
    (trace (send (enc question y n ans-key)) (recv y)))
  (defrole init-negative
    (vars (y n data) (question text) (ans-key akey))
    (trace (send (enc question y n ans-key)) (recv n)))
  (defrole resp-positive
    (vars (y n data) (question text) (ans-key akey))
    (trace (recv (enc question y n ans-key)) (send y)))
  (defrole resp-negative
    (vars (y n data) (question text) (ans-key akey))
    (trace (recv (enc question y n ans-key)) (send n)))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton yes-or-no
  (vars (y n data) (question text) (ans-key akey))
  (defstrand init-positive 1 (y y) (n n) (question question)
    (ans-key ans-key))
  (deflistener y)
  (non-orig (invk ans-key))
  (uniq-orig y)
  (traces ((send (enc question y n ans-key))) ((recv y) (send y)))
  (label 4)
  (unrealized (1 0))
  (preskeleton)
  (origs (y (0 0)))
  (comment "Not a skeleton"))

(defskeleton yes-or-no
  (vars (y n data) (question text) (ans-key akey))
  (defstrand init-positive 1 (y y) (n n) (question question)
    (ans-key ans-key))
  (deflistener y)
  (precedes ((0 0) (1 0)))
  (non-orig (invk ans-key))
  (uniq-orig y)
  (traces ((send (enc question y n ans-key))) ((recv y) (send y)))
  (label 5)
  (parent 4)
  (unrealized (1 0))
  (origs (y (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton yes-or-no
  (vars (y n data) (question text) (ans-key akey))
  (defstrand init-positive 1 (y y) (n n) (question question)
    (ans-key ans-key))
  (deflistener y)
  (defstrand resp-positive 2 (y y) (n n) (question question)
    (ans-key ans-key))
  (precedes ((0 0) (2 0)) ((2 1) (1 0)))
  (non-orig (invk ans-key))
  (uniq-orig y)
  (operation nonce-test (added-strand resp-positive 2) y (1 0)
    (enc question y n ans-key))
  (traces ((send (enc question y n ans-key))) ((recv y) (send y))
    ((recv (enc question y n ans-key)) (send y)))
  (label 6)
  (parent 5)
  (realized)
  (shape)
  (maps ((0 1) ((y y) (ans-key ans-key) (n n) (question question))))
  (origs (y (0 0))))

(comment "Nothing left to do")

(defprotocol yes-or-no basic
  (defrole init-positive
    (vars (y n data) (question text) (ans-key akey))
    (trace (send (enc question y n ans-key)) (recv y)))
  (defrole init-negative
    (vars (y n data) (question text) (ans-key akey))
    (trace (send (enc question y n ans-key)) (recv n)))
  (defrole resp-positive
    (vars (y n data) (question text) (ans-key akey))
    (trace (recv (enc question y n ans-key)) (send y)))
  (defrole resp-negative
    (vars (y n data) (question text) (ans-key akey))
    (trace (recv (enc question y n ans-key)) (send n)))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton yes-or-no
  (vars (n y data) (question text) (ans-key akey))
  (defstrand init-positive 1 (y y) (n n) (question question)
    (ans-key ans-key))
  (deflistener n)
  (non-orig (invk ans-key))
  (uniq-orig n)
  (traces ((send (enc question y n ans-key))) ((recv n) (send n)))
  (label 7)
  (unrealized (1 0))
  (preskeleton)
  (origs (n (0 0)))
  (comment "Not a skeleton"))

(defskeleton yes-or-no
  (vars (n y data) (question text) (ans-key akey))
  (defstrand init-positive 1 (y y) (n n) (question question)
    (ans-key ans-key))
  (deflistener n)
  (precedes ((0 0) (1 0)))
  (non-orig (invk ans-key))
  (uniq-orig n)
  (traces ((send (enc question y n ans-key))) ((recv n) (send n)))
  (label 8)
  (parent 7)
  (unrealized (1 0))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton yes-or-no
  (vars (n y data) (question text) (ans-key akey))
  (defstrand init-positive 1 (y y) (n n) (question question)
    (ans-key ans-key))
  (deflistener n)
  (defstrand resp-negative 2 (y y) (n n) (question question)
    (ans-key ans-key))
  (precedes ((0 0) (2 0)) ((2 1) (1 0)))
  (non-orig (invk ans-key))
  (uniq-orig n)
  (operation nonce-test (added-strand resp-negative 2) n (1 0)
    (enc question y n ans-key))
  (traces ((send (enc question y n ans-key))) ((recv n) (send n))
    ((recv (enc question y n ans-key)) (send n)))
  (label 9)
  (parent 8)
  (realized)
  (shape)
  (maps ((0 1) ((n n) (ans-key ans-key) (y y) (question question))))
  (origs (n (0 0))))

(comment "Nothing left to do")
