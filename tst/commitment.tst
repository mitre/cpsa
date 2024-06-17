(herald commitment)

(comment "CPSA 4.4.4")
(comment "All input read from tst/commitment.scm")

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
    (forall ((z strd) (a b name) (n data) (quote text) (sealed mesg))
      (implies
        (and (p "auctioneer" z (idx 4))
          (p "auctioneer" "sealed" z sealed)
          (p "auctioneer" "quote" z quote) (p "auctioneer" "n" z n)
          (p "auctioneer" "b" z b) (p "auctioneer" "a" z a))
        (= sealed (hash a b n quote)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton commit
  (vars (sealed mesg) (n data) (quote outcome text) (a b name))
  (defstrand auctioneer 4 (sealed sealed) (n n) (quote quote)
    (outcome outcome) (a a) (b b))
  (non-orig (privk "sig" a))
  (traces
    ((recv (enc "bid" sealed (privk "sig" a)))
      (send (enc "receipt" sealed (privk "sig" b))) (recv (cat n quote))
      (send (enc "result" a b n quote outcome (privk "sig" b)))))
  (label 0)
  (unrealized (0 0))
  (origs)
  (comment "Not closed under rules"))

(defskeleton commit
  (vars (n data) (quote outcome text) (a b name))
  (defstrand auctioneer 4 (sealed (hash a b n quote)) (n n)
    (quote quote) (outcome outcome) (a a) (b b))
  (non-orig (privk "sig" a))
  (rule cheq-auctioneer-4)
  (traces
    ((recv (enc "bid" (hash a b n quote) (privk "sig" a)))
      (send (enc "receipt" (hash a b n quote) (privk "sig" b)))
      (recv (cat n quote))
      (send (enc "result" a b n quote outcome (privk "sig" b)))))
  (label 1)
  (parent 0)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton commit
  (vars (n data) (quote outcome text) (a b name))
  (defstrand auctioneer 4 (sealed (hash a b n quote)) (n n)
    (quote quote) (outcome outcome) (a a) (b b))
  (defstrand bidder 1 (n n) (quote quote) (a a) (b b))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sig" a))
  (operation encryption-test (added-strand bidder 1)
    (enc "bid" (hash a b n quote) (privk "sig" a)) (0 0))
  (strand-map 0)
  (traces
    ((recv (enc "bid" (hash a b n quote) (privk "sig" a)))
      (send (enc "receipt" (hash a b n quote) (privk "sig" b)))
      (recv (cat n quote))
      (send (enc "result" a b n quote outcome (privk "sig" b))))
    ((send (enc "bid" (hash a b n quote) (privk "sig" a)))))
  (label 2)
  (parent 1)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (n n) (quote quote) (outcome outcome)
        (sealed (hash a b n quote)))))
  (origs))

(comment "Nothing left to do")

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
    (forall ((z strd) (a b name) (n data) (quote text) (sealed mesg))
      (implies
        (and (p "auctioneer" z (idx 4))
          (p "auctioneer" "sealed" z sealed)
          (p "auctioneer" "quote" z quote) (p "auctioneer" "n" z n)
          (p "auctioneer" "b" z b) (p "auctioneer" "a" z a))
        (= sealed (hash a b n quote)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton commit
  (vars (sealed mesg) (a b name))
  (defstrand auctioneer 2 (sealed sealed) (a a) (b b))
  (non-orig (privk "sig" a))
  (traces
    ((recv (enc "bid" sealed (privk "sig" a)))
      (send (enc "receipt" sealed (privk "sig" b)))))
  (label 3)
  (unrealized (0 0))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton commit
  (vars (n data) (quote text) (a b b-0 name))
  (defstrand auctioneer 2 (sealed (hash a b-0 n quote)) (a a) (b b))
  (defstrand bidder 1 (n n) (quote quote) (a a) (b b-0))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sig" a))
  (operation encryption-test (added-strand bidder 1)
    (enc "bid" (hash a b-0 n quote) (privk "sig" a)) (0 0))
  (strand-map 0)
  (traces
    ((recv (enc "bid" (hash a b-0 n quote) (privk "sig" a)))
      (send (enc "receipt" (hash a b-0 n quote) (privk "sig" b))))
    ((send (enc "bid" (hash a b-0 n quote) (privk "sig" a)))))
  (label 4)
  (parent 3)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (sealed (hash a b-0 n quote)))))
  (origs))

(defskeleton commit
  (vars (n data) (trash text) (a b name))
  (defstrand auctioneer 2 (sealed (hash n trash)) (a a) (b b))
  (defstrand bid-trash 1 (n n) (trash trash) (a a))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sig" a))
  (operation encryption-test (added-strand bid-trash 1)
    (enc "bid" (hash n trash) (privk "sig" a)) (0 0))
  (strand-map 0)
  (traces
    ((recv (enc "bid" (hash n trash) (privk "sig" a)))
      (send (enc "receipt" (hash n trash) (privk "sig" b))))
    ((send (enc "bid" (hash n trash) (privk "sig" a)))))
  (label 5)
  (parent 3)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (sealed (hash n trash)))))
  (origs))

(comment "Nothing left to do")

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
    (forall ((z strd) (a b name) (n data) (quote text) (sealed mesg))
      (implies
        (and (p "auctioneer" z (idx 4))
          (p "auctioneer" "sealed" z sealed)
          (p "auctioneer" "quote" z quote) (p "auctioneer" "n" z n)
          (p "auctioneer" "b" z b) (p "auctioneer" "a" z a))
        (= sealed (hash a b n quote)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton commit
  (vars (n data) (quote outcome text) (a b name))
  (defstrand auctioneer 4 (sealed (hash a b n quote)) (n n)
    (quote quote) (outcome outcome) (a a) (b b))
  (defstrand bidder 1 (n n) (quote quote) (a a) (b b))
  (non-orig (privk "sig" a))
  (uniq-gen n)
  (traces
    ((recv (enc "bid" (hash a b n quote) (privk "sig" a)))
      (send (enc "receipt" (hash a b n quote) (privk "sig" b)))
      (recv (cat n quote))
      (send (enc "result" a b n quote outcome (privk "sig" b))))
    ((send (enc "bid" (hash a b n quote) (privk "sig" a)))))
  (label 6)
  (unrealized (0 0) (0 2))
  (preskeleton)
  (origs)
  (ugens (n (1 0)))
  (comment "Not a skeleton"))

(defskeleton commit
  (vars (n data) (quote outcome text) (a b name))
  (defstrand auctioneer 4 (sealed (hash a b n quote)) (n n)
    (quote quote) (outcome outcome) (a a) (b b))
  (defstrand bidder 1 (n n) (quote quote) (a a) (b b))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sig" a))
  (uniq-gen n)
  (traces
    ((recv (enc "bid" (hash a b n quote) (privk "sig" a)))
      (send (enc "receipt" (hash a b n quote) (privk "sig" b)))
      (recv (cat n quote))
      (send (enc "result" a b n quote outcome (privk "sig" b))))
    ((send (enc "bid" (hash a b n quote) (privk "sig" a)))))
  (label 7)
  (parent 6)
  (unrealized (0 2))
  (origs)
  (ugens (n (1 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton commit
  (vars (n data) (outcome quote text) (a b name))
  (defstrand auctioneer 4 (sealed (hash a b n quote)) (n n)
    (quote quote) (outcome outcome) (a a) (b b))
  (defstrand bidder 3 (n n) (quote quote) (a a) (b b))
  (precedes ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk "sig" a))
  (uniq-gen n)
  (operation nonce-test (displaced 1 2 bidder 3) n (0 2))
  (strand-map 0 1)
  (traces
    ((recv (enc "bid" (hash a b n quote) (privk "sig" a)))
      (send (enc "receipt" (hash a b n quote) (privk "sig" b)))
      (recv (cat n quote))
      (send (enc "result" a b n quote outcome (privk "sig" b))))
    ((send (enc "bid" (hash a b n quote) (privk "sig" a)))
      (recv (enc "receipt" (hash a b n quote) (privk "sig" b)))
      (send (cat n quote))))
  (label 8)
  (parent 7)
  (realized)
  (shape)
  (maps ((0 1) ((n n) (quote quote) (outcome outcome) (a a) (b b))))
  (origs)
  (ugens (n (1 0))))

(comment "Nothing left to do")
