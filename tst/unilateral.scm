(herald unilateral)

(defprotocol unilateral basic
  (defrole init
     (vars (n text) (k akey))
     (trace
      (send (enc n k))
      (recv n))
     (uniq-orig n))
  (defrole resp
     (vars (n text) (k akey))
     (trace
      (recv (enc n k))
      (send n))))

(defskeleton unilateral
   (vars (k akey))
   (defstrand init 2 (k k))
   (non-orig (invk k)))

(defskeleton unilateral
   (vars (n text) (k akey))
   (defstrand resp 2 (n n) (k k))
   (pen-non-orig n)
   (non-orig (invk k)))

;;; The same two problems posed using security goals.  The goals were
;;; taken from the output of cpsasas.

(defgoal unilateral
  (forall ((n text) (k akey) (z z-0 node))
    (implies
      (and (p "init" 0 z) (p "init" 1 z-0) (p "init" "n" z-0 n)
        (p "init" "k" z-0 k) (str-prec z z-0) (non (invk k))
        (uniq-at n z))
      (exists ((z-1 z-2 node))
        (and (p "resp" 0 z-1) (p "resp" 1 z-2) (p "resp" "n" z-2 n)
          (p "resp" "k" z-2 k) (prec z z-1) (prec z-2 z-0)
          (str-prec z-1 z-2))))))

(defgoal unilateral
  (forall ((n text) (k akey) (z node))
    (implies
      (and (p "resp" 1 z) (p "resp" "n" z n) (p "resp" "k" z k)
        (non (invk k)) (pnon n))
      (exists ((k-0 akey) (z-0 z-1 node))
        (and (p "resp" 0 z-0) (p "init" 0 z-1) (p "init" "n" z-1 n)
          (p "init" "k" z-1 k-0) (prec z-1 z-0) (str-prec z-0 z)
          (uniq-at n z-1))))))
