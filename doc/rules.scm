(herald "Inequality constraint using facts and rules"
	(comment "First skeleton should have a shape,"
		 "second should be dead."))

(defprotocol neq-test basic
  (defrole init
    (vars (n1 n2 text) (k skey))
    (trace
     (send (cat n1 (enc n1 n2 k)))
     (recv n2))
    (non-orig k)
    (uniq-orig n1 n2))
  (defrule neq
    (forall ((a mesg))
	    (implies
	     (fact neq a a)
	     (false)))))

;;; With no inequality fact,
;;; a shape should be found where n1 = n2.
(defskeleton neq-test
  (vars)
  (defstrand init 2))

;;; With an inequality fact,
;;; no shape should exist.
(defskeleton neq-test
   (vars (n1 n2 text))
   (defstrand init 2 (n1 n1) (n2 n2))
   (facts (neq n1 n2)))			;  assert n1 != n2
