(herald "Electronic Purchase with Money Order Protocol"
  (comment "Annotated with trust management formulas"))

(defprotocol epmo basic
  (defrole bank
    (vars (b c m name) (hash akey) (nc nm nb data) (price text))
    (trace
     (recv (enc c nc nm price (pubk b)))
     (send (cat (enc (enc c nc nb nm price hash) (privk b))
		(enc nc nb (pubk c))))
     (recv (enc (enc b nb nm hash) (privk m))))
    (non-orig (invk hash))
    (uniq-orig nb)
    (annotations b
      (1
        (implies
          (and (forall ((pm name)) (says c (transfer b price pm nm)))
            (forall ((pm name)) (says pm (transfer b price pm nm))))
          (forall ((pm name)) (transfer b price pm nm))))
      (2
        (and (says c (transfer b price m nm))
          (says m (transfer b price m nm))))))
  (defrole customer
    (vars (b c m name) (hash akey) (nb nc nm data) (goods price text))
    (trace
     (send (enc c nc goods price (pubk m)))
     (recv (enc nc nm m goods price (pubk c)))
     (send (enc c nc nm price (pubk b)))
     (recv (cat (enc (enc c nc nb nm price hash) (privk b))
		(enc nc nb (pubk c))))
     (send (cat (enc (enc c nc nb nm price hash) (privk b)) nb)))
    (non-orig (invk hash))
    (uniq-orig nc)
    (annotations c
      (1
        (says m
          (forall ((pb name))
            (implies (transfer pb price m nm) (ship m goods c)))))
      (3
        (says b
          (implies
            (and (forall ((pm name)) (says c (transfer b price pm nm)))
              (forall ((pm name)) (says m (transfer b price pm nm))))
            (transfer b price m nm))))
      (4 (transfer b price m nm))))
  (defrole merchant
    (vars (b c m name) (hash akey) (nb nc nm data) (goods price text))
    (trace
     (recv (enc c nc goods price (pubk m)))
     (send (enc nc nm m goods price (pubk c)))
     (recv (cat (enc (enc c nc nb nm price hash) (privk b)) nb))
     (send (enc (enc b nb nm hash) (privk m))))
    (non-orig (invk hash))
    (uniq-orig nm)
    (annotations m
      (1
        (forall ((pb name))
          (implies (transfer pb price m nm) (ship m goods c))))
      (2
        (and
          (says b
            (implies
              (and
                (forall ((pm name)) (says c (transfer b price pm nm)))
                (forall ((pm name)) (says m (transfer b price pm nm))))
              (transfer b price m nm)))
          (says c (transfer b price m nm))))
      (3 (and (transfer b price m nm) (ship m goods c))))))

(defskeleton epmo (vars (b c m name))
  (defstrand customer 5 (b b) (c c) (m m))
  (non-orig (privk b) (privk c) (privk m)))

(defskeleton epmo (vars (b c m name) (goods name))
  (defstrand bank 3 (b b) (c c) (m m))
  (non-orig (privk b) (privk c) (privk m)))

(defskeleton epmo (vars (b c m name))
  (defstrand merchant 4 (b b) (c c) (m m))
  (non-orig (privk b) (privk c) (privk m)))
