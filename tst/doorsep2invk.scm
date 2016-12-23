(herald doorsep2invk (comment "Door Simple Example Protocol"))

(defprotocol doorsep basic
  (defrole init
    (vars (self peer akey) (skey skey) (data text))
    (trace (send (enc (enc skey (invk self)) peer))
      (recv (enc data skey)) (send data))
    (uniq-orig skey))
  (defrole resp
    (vars (self peer akey) (skey skey) (data text))
    (trace (recv (enc (enc skey (invk peer)) self))
      (send (enc data skey)) (recv data))
    (uniq-orig data))
  (comment "Doorsep's protocol using unnamed asymmetric keys"))

(defgoal doorsep
  (forall
    ((akey+1 akey) (text+0 text) (akey+0 akey+3 akey) (skey+0 skey)
      (node+3 node+2 node+1 node+0 node))
    (implies
      (and (p "init" 0 node+0) (p "resp" 0 node+1) (p "resp" 1 node+2)
        (p "resp" 2 node+3) (p "init" "skey" node+0 skey+0)
        (p "init" "self" node+0 (invk akey+3))
        (p "init" "peer" node+0 akey+0) (p "resp" "data" node+2 text+0)
        (p "resp" "data" node+3 text+0) (p "resp" "skey" node+1 skey+0)
        (p "resp" "skey" node+2 skey+0) (p "resp" "skey" node+3 skey+0)
        (p "resp" "peer" node+1 (invk akey+3))
        (p "resp" "peer" node+2 (invk akey+3))
        (p "resp" "peer" node+3 (invk akey+3))
        (p "resp" "self" node+1 akey+1) (p "resp" "self" node+2 akey+1)
        (p "resp" "self" node+3 akey+1) (str-prec node+1 node+2)
        (str-prec node+1 node+3) (str-prec node+2 node+3)
        (prec node+0 node+1) (non (invk akey+0)) (non akey+3)
        (uniq-at text+0 node+2) (uniq-at skey+0 node+0)) (and))))
