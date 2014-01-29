(herald "Electronic Purchase with Money Order Protocol Variant"
  (bound 12)
  (comment "This version includes account numbers in exchanges"
	   "This version uses sorts to avoid confusion"
	   "between a nonce and other data"))

(defprotocol sorted_epmo_acctnum basic
  (defrole bank
    (vars (b c m name) (acctnum price text) (hash name) (nc nm nb data))
    (trace
     (recv (enc c nc nm acctnum price (pubk b)))
     (send (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
		(enc nc nb (pubk c))))
     (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    (non-orig (privk hash))
    (annotations b
      (1
        (forall ((pm name))
          (implies
            (and (authtransfer c acctnum b price pm nm)
              (reqtransfer pm b price pm nm))
            (dotransfer acctnum b price pm nm))))
      (2
        (and (says c (authtransfer c acctnum b price m nm))
          (says m (reqtransfer m b price m nm))))))
  (defrole customer
    (vars (b c m hash name) (acctnum goods price text) (nc nm nb data))
    (trace
     (send (enc c nc goods (pubk m)))
     (recv (enc nc nm m price (pubk c)))
     (send (enc c nc nm acctnum price (pubk b)))
     (recv (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
		(enc nc nb (pubk c))))
     (send (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
		nb)))
    (non-orig (privk b) (privk hash))
    (uniq-orig nc)
    (annotations c
      (1
        (says m
          (implies
            (exists ((acctnum2 text))
              (dotransfer acctnum2 b price m nm)) (doship m goods c))))
      (3
        (says b
          (forall ((pm name))
            (implies
              (and (authtransfer c acctnum b price m nm)
                (reqtransfer pm b price pm nm))
              (dotransfer acctnum b price pm nm)))))
      (4 (authtransfer c acctnum b price m nm))))
  (defrole merchant (vars (b c m hash name) (goods price text) (nc nm nb data))
    (trace
     (recv (enc c nc goods (pubk m)))
     (send (enc nc nm m price (pubk c)))
     (recv (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
		nb))
     (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    (non-orig (privk hash))
    (uniq-orig nm)
    (annotations m
      (1
        (implies
          (exists ((acctnum2 text)) (dotransfer acctnum2 b price m nm))
          (doship m goods c)))
      (2
        (and
          (says b
            (forall ((pm name))
              (exists ((acctnum2 text))
                (implies
                  (and (authtransfer c acctnum2 b price m nm)
                    (reqtransfer pm b price pm nm))
                  (dotransfer acctnum2 b price pm nm)))))
          (says c
            (exists ((acctnum2 text))
              (authtransfer c acctnum2 b price m nm)))))
      (3 (and (reqtransfer m b price m nm) (doship m goods c))))))

(defskeleton sorted_epmo_acctnum
  (vars (b m c name) (nm nc nb data) (hash name))
  (defstrand merchant 4 (b b) (m m) (c c) (nm nm) (nc nc) (nb nb) (hash hash))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nc nb))

(defskeleton sorted_epmo_acctnum
  (vars (b m c name) (nm nb nc data) (hash name) (price acctnum text))
  (defstrand bank 3 (b b) (m m) (c c) (nm nm) (nb nb) (nc nc) (hash hash))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nc nb))
