(herald rule-node)

(defprotocol rule-order basic
  (defrole init
    (vars (s t text))
    (trace
     (send (cat s t))
     (recv (cat t s))))

  (defrule le-lt
    (forall ((z1 z2 strd)(i1 i2 indx))
	    (implies
	     (fact le z1 i1 z2 i2)
	     (or
	      (and (= z1 z2) (= i1 i2))
	      (fact lt z1 i1 z2 i2)))))

  (defrule lt-le
    (forall ((z1 z2 strd)(i1 i2 indx))
	    (implies
	     (fact lt z1 i1 z2 i2)		     
	     (fact le z1 i1 z2 i2))))
  
  (defrule prec-lt
    (forall ((z1 z2 strd)(i1 i2 indx))
	    (implies
	     (prec z1 i1 z2 i2)
	     (or 
	      (fact lt z1 i1 z2 i2)))))
  )

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (facts (le 0 0 0 1)))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (facts (le 1 0 0 1) (le 0 0 0 1)))

(defprotocol rule-order-prec basic
  (defrole init
    (vars (s t text))
    (trace
     (send (cat s t))
     (recv (cat t s))))

  
  
  (defrule prec-tell-me
    (forall ((z1 z2 strd) (i1 i2 indx))
	    (implies 
	     (prec z1 i1 z2 i2)
	     (fact tell-me z1 i1 z2 i2))))
  )


(defskeleton rule-order-prec 
  (vars (s t text))
  (defstrand init 2 (s t) (t s))
  ;;   (facts (le 0 0 0 1))
  )

(defskeleton rule-order-prec 
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  ;; (facts (le 1 0 0 1) (le 0 0 0 1))
  )


