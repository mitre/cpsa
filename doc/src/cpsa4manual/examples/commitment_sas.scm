(herald commitment)

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

(comment "All input read from commitment.scm")

(defprotocol commit basic
  (defrole bidder
    (vars (a b name) (n data) (quote outcome text))
    (trace (send (enc "bid" (hash a b n quote) (privk "sig" a)))
      (recv (enc "receipt" (hash a b n quote) (privk "sig" b)))
      (send (cat n quote))
      (recv (enc "result" a b n quote outcome (privk "sig" b)))))
  (defrole bid-trash
    (vars (a b name) (n data) (trash text))
    (trace (send (enc "bid" (hash n trash) (privk "sig" a)))
      (recv (enc "receipt" (hash n trash) (privk "sig" b)))))
  (defrole auctioneer
    (vars (a b name) (n data) (quote outcome text) (sealed mesg))
    (trace (recv (enc "bid" sealed (privk "sig" a)))
      (send (enc "receipt" sealed (privk "sig" b))) (recv (cat n quote))
      (send (enc "result" a b n quote outcome (privk "sig" b)))))
  (defrule cheq-auctioneer-4
    (forall ((z strd) (quote text) (n data) (b a name) (sealed mesg))
      (implies
        (and (p "auctioneer" z (idx 4)) (p "auctioneer" "quote" z quote)
          (p "auctioneer" "n" z n) (p "auctioneer" "b" z b)
          (p "auctioneer" "a" z a) (p "auctioneer" "sealed" z sealed))
        (= sealed (hash a b n quote)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal commit
  (forall
    ((sealed mesg) (n data) (quote outcome text) (a b name) (z strd))
    (implies
      (and (p "auctioneer" z 4) (p "auctioneer" "sealed" z sealed)
        (p "auctioneer" "n" z n) (p "auctioneer" "quote" z quote)
        (p "auctioneer" "outcome" z outcome) (p "auctioneer" "a" z a)
        (p "auctioneer" "b" z b) (non (privk "sig" a)))
      (exists ((z-0 strd))
        (and (= sealed (hash a b n quote)) (p "bidder" z-0 1)
          (p "auctioneer" "sealed" z (hash a b n quote))
          (p "bidder" "n" z-0 n) (p "bidder" "quote" z-0 quote)
          (p "bidder" "a" z-0 a) (p "bidder" "b" z-0 b)
          (prec z-0 0 z 0))))))

(defprotocol commit basic
  (defrole bidder
    (vars (a b name) (n data) (quote outcome text))
    (trace (send (enc "bid" (hash a b n quote) (privk "sig" a)))
      (recv (enc "receipt" (hash a b n quote) (privk "sig" b)))
      (send (cat n quote))
      (recv (enc "result" a b n quote outcome (privk "sig" b)))))
  (defrole bid-trash
    (vars (a b name) (n data) (trash text))
    (trace (send (enc "bid" (hash n trash) (privk "sig" a)))
      (recv (enc "receipt" (hash n trash) (privk "sig" b)))))
  (defrole auctioneer
    (vars (a b name) (n data) (quote outcome text) (sealed mesg))
    (trace (recv (enc "bid" sealed (privk "sig" a)))
      (send (enc "receipt" sealed (privk "sig" b))) (recv (cat n quote))
      (send (enc "result" a b n quote outcome (privk "sig" b)))))
  (defrule cheq-auctioneer-4
    (forall ((z strd) (quote text) (n data) (b a name) (sealed mesg))
      (implies
        (and (p "auctioneer" z (idx 4)) (p "auctioneer" "quote" z quote)
          (p "auctioneer" "n" z n) (p "auctioneer" "b" z b)
          (p "auctioneer" "a" z a) (p "auctioneer" "sealed" z sealed))
        (= sealed (hash a b n quote)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal commit
  (forall ((sealed mesg) (a b name) (z strd))
    (implies
      (and (p "auctioneer" z 2) (p "auctioneer" "sealed" z sealed)
        (p "auctioneer" "a" z a) (p "auctioneer" "b" z b)
        (non (privk "sig" a)))
      (or
        (exists ((n data) (quote text) (b-0 name) (z-0 strd))
          (and (= sealed (hash a b-0 n quote)) (p "bidder" z-0 1)
            (p "auctioneer" "sealed" z (hash a b-0 n quote))
            (p "bidder" "n" z-0 n) (p "bidder" "quote" z-0 quote)
            (p "bidder" "a" z-0 a) (p "bidder" "b" z-0 b-0)
            (prec z-0 0 z 0)))
        (exists ((n data) (trash text) (z-0 strd))
          (and (= sealed (hash n trash)) (p "bid-trash" z-0 1)
            (p "auctioneer" "sealed" z (hash n trash))
            (p "bid-trash" "n" z-0 n) (p "bid-trash" "trash" z-0 trash)
            (p "bid-trash" "a" z-0 a) (prec z-0 0 z 0)))))))

(defprotocol commit basic
  (defrole bidder
    (vars (a b name) (n data) (quote outcome text))
    (trace (send (enc "bid" (hash a b n quote) (privk "sig" a)))
      (recv (enc "receipt" (hash a b n quote) (privk "sig" b)))
      (send (cat n quote))
      (recv (enc "result" a b n quote outcome (privk "sig" b)))))
  (defrole bid-trash
    (vars (a b name) (n data) (trash text))
    (trace (send (enc "bid" (hash n trash) (privk "sig" a)))
      (recv (enc "receipt" (hash n trash) (privk "sig" b)))))
  (defrole auctioneer
    (vars (a b name) (n data) (quote outcome text) (sealed mesg))
    (trace (recv (enc "bid" sealed (privk "sig" a)))
      (send (enc "receipt" sealed (privk "sig" b))) (recv (cat n quote))
      (send (enc "result" a b n quote outcome (privk "sig" b)))))
  (defrule cheq-auctioneer-4
    (forall ((z strd) (quote text) (n data) (b a name) (sealed mesg))
      (implies
        (and (p "auctioneer" z (idx 4)) (p "auctioneer" "quote" z quote)
          (p "auctioneer" "n" z n) (p "auctioneer" "b" z b)
          (p "auctioneer" "a" z a) (p "auctioneer" "sealed" z sealed))
        (= sealed (hash a b n quote)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal commit
  (forall ((n data) (quote outcome text) (a b name) (z z-0 strd))
    (implies
      (and (p "auctioneer" z 4) (p "bidder" z-0 1)
        (p "auctioneer" "sealed" z (hash a b n quote))
        (p "auctioneer" "n" z n) (p "auctioneer" "quote" z quote)
        (p "auctioneer" "outcome" z outcome) (p "auctioneer" "a" z a)
        (p "auctioneer" "b" z b) (p "bidder" "n" z-0 n)
        (p "bidder" "quote" z-0 quote) (p "bidder" "a" z-0 a)
        (p "bidder" "b" z-0 b) (non (privk "sig" a)) (ugen n))
      (and (p "bidder" z-0 3) (prec z-0 0 z 0) (prec z-0 2 z 2)))))
