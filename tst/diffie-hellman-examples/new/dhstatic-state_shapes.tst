(comment "CPSA 4.4.4")
(comment "Extracted shapes")

(herald dhstatic-state (algebra diffie-hellman) (bound 16))

(comment "CPSA 4.4.4")

(comment "All input read from dhstatic-state.scm")

(comment "Strand count bounded at 16")

(defprotocol dhstatic-state diffie-hellman
  (defrole cert
    (vars (subj ca name) (serial data) (galpha mesg))
    (trace (recv (sig (cert-req subj galpha ca) (privk "sig" subj)))
      (send (sig (cert subj galpha ca serial) (privk "sig" ca))))
    (uniq-orig serial)
    (comment "Certificate Authority"))
  (defrole get-cert
    (vars (self ca name) (serial data) (ra rndx) (static-key locn)
      (ignore mesg))
    (trace
      (send (sig (cert-req self (exp (gen) ra) ca) (privk "sig" self)))
      (recv (sig (cert self (exp (gen) ra) ca serial) (privk "sig" ca)))
      (load static-key ignore)
      (stor static-key (cat "privkey" self ra serial ca)))
    (uniq-gen ra)
    (comment "Get certified"))
  (defrole init
    (vars (a b ca name) (ra rndx) (serial-a serial-b data) (alpha expt)
      (n text) (static-key locn))
    (trace (load static-key (cat "privkey" a ra serial-a ca))
      (recv
        (sig (cert b (exp (gen) alpha) ca serial-b) (privk "sig" ca)))
      (send (enc n a b serial-a serial-b (exp (gen) (mul ra alpha))))
      (recv n))
    (uniq-orig n)
    (gen-st (cat "privkey" a ra serial-a ca))
    (facts (neq a b))
    (comment "Initiator is A"))
  (defrole resp
    (vars (a b ca name) (rb rndx) (serial-b serial-a data) (alpha expt)
      (n text) (static-key locn))
    (trace (load static-key (cat "privkey" b rb serial-b ca))
      (recv
        (sig (cert a (exp (gen) alpha) ca serial-a) (privk "sig" ca)))
      (recv (enc n a b serial-a serial-b (exp (gen) (mul rb alpha))))
      (send n))
    (facts (neq a b))
    (gen-st (cat "privkey" b rb serial-b ca))
    (comment "Responder is B"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule fact-init-neq0
    (forall ((z strd) (b a name))
      (implies
        (and (p "init" z (idx 2)) (p "init" "a" z a) (p "init" "b" z b))
        (fact neq a b))))
  (defgenrule fact-resp-neq0
    (forall ((z strd) (b a name))
      (implies
        (and (p "resp" z (idx 2)) (p "resp" "a" z a) (p "resp" "b" z b))
        (fact neq a b))))
  (defgenrule trRl_get-cert-at-3
    (forall ((z strd))
      (implies (p "get-cert" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_get-cert-at-2
    (forall ((z strd))
      (implies (p "get-cert" z (idx 4)) (trans z (idx 2)))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (a name) (ra rndx) (serial-a data) (ca name))
      (implies
        (and (p "init" z (idx 1)) (p "init" "ca" z ca)
          (p "init" "serial-a" z serial-a) (p "init" "ra" z ra)
          (p "init" "a" z a))
        (gen-st (cat "privkey" a ra serial-a ca)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (b name) (rb rndx) (serial-b data) (ca name))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "ca" z ca)
          (p "resp" "serial-b" z serial-b) (p "resp" "rb" z rb)
          (p "resp" "b" z b))
        (gen-st (cat "privkey" b rb serial-b ca)))))
  (lang (cert-req (tupl 3)) (cert (tupl 4)) (sig sign)))

(defskeleton dhstatic-state
  (vars (serial-a serial-b data) (n text) (ca b a name) (pt pval)
    (static-key locn) (ra rndx) (alpha expt))
  (defstrand init 4 (serial-a serial-a) (serial-b serial-b) (n n) (a a)
    (b b) (ca ca) (static-key static-key) (ra ra) (alpha alpha))
  (non-orig (privk "sig" ca) (privk "sig" b))
  (uniq-orig n)
  (traces
    ((load static-key (cat pt "privkey" a ra serial-a ca))
      (recv
        (sig (cert b (exp (gen) alpha) ca serial-b) (privk "sig" ca)))
      (send (enc n a b serial-a serial-b (exp (gen) (mul ra alpha))))
      (recv n)))
  (label 0)
  (unrealized (0 1))
  (origs (n (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhstatic-state
  (vars (ignore ignore-0 mesg) (serial-a serial-b data) (n text)
    (b a ca name) (pt pt-0 pt-1 pt-2 pval)
    (static-key static-key-0 locn) (ra ra-0 rndx))
  (defstrand init 4 (serial-a serial-a) (serial-b serial-b) (n n) (a a)
    (b b) (ca ca) (static-key static-key) (ra ra) (alpha ra-0))
  (defstrand get-cert 4 (ignore ignore) (serial serial-a) (self a)
    (ca ca) (static-key static-key) (ra ra))
  (defstrand cert 2 (galpha (exp (gen) ra)) (serial serial-a) (subj a)
    (ca ca))
  (defstrand cert 2 (galpha (exp (gen) ra-0)) (serial serial-b) (subj b)
    (ca ca))
  (defstrand resp 4 (serial-b serial-b) (serial-a serial-a) (n n) (a a)
    (b b) (ca ca) (static-key static-key-0) (rb ra-0) (alpha ra))
  (defstrand get-cert 4 (ignore ignore-0) (serial serial-b) (self b)
    (ca ca) (static-key static-key-0) (ra ra-0))
  (precedes ((0 2) (4 2)) ((1 0) (2 0)) ((1 3) (0 0)) ((2 1) (1 1))
    ((2 1) (4 1)) ((3 1) (0 1)) ((3 1) (5 1)) ((4 3) (0 3))
    ((5 0) (3 0)) ((5 3) (4 0)))
  (non-orig (privk "sig" b) (privk "sig" ca))
  (uniq-orig serial-a serial-b n)
  (uniq-gen ra ra-0)
  (gen-st (cat "privkey" b ra-0 serial-b ca)
    (cat "privkey" a ra serial-a ca))
  (facts (neq a b) (neq b a))
  (leads-to ((1 3) (0 0)) ((5 3) (4 0)))
  (rule fact-resp-neq0 trRl_get-cert-at-2 trRl_get-cert-at-3)
  (operation channel-test (displaced 4 6 get-cert 4)
    (ch-msg static-key-0 (cat pt-1 "privkey" b ra-1 serial-b ca)) (5 0))
  (strand-map 0 1 2 3 5 4)
  (traces
    ((load static-key (cat pt "privkey" a ra serial-a ca))
      (recv
        (sig (cert b (exp (gen) ra-0) ca serial-b) (privk "sig" ca)))
      (send (enc n a b serial-a serial-b (exp (gen) (mul ra ra-0))))
      (recv n))
    ((send (sig (cert-req a (exp (gen) ra) ca) (privk "sig" a)))
      (recv (sig (cert a (exp (gen) ra) ca serial-a) (privk "sig" ca)))
      (load static-key (cat pt-0 ignore))
      (stor static-key (cat pt "privkey" a ra serial-a ca)))
    ((recv (sig (cert-req a (exp (gen) ra) ca) (privk "sig" a)))
      (send (sig (cert a (exp (gen) ra) ca serial-a) (privk "sig" ca))))
    ((recv (sig (cert-req b (exp (gen) ra-0) ca) (privk "sig" b)))
      (send
        (sig (cert b (exp (gen) ra-0) ca serial-b) (privk "sig" ca))))
    ((load static-key-0 (cat pt-1 "privkey" b ra-0 serial-b ca))
      (recv (sig (cert a (exp (gen) ra) ca serial-a) (privk "sig" ca)))
      (recv (enc n a b serial-a serial-b (exp (gen) (mul ra ra-0))))
      (send n))
    ((send (sig (cert-req b (exp (gen) ra-0) ca) (privk "sig" b)))
      (recv
        (sig (cert b (exp (gen) ra-0) ca serial-b) (privk "sig" ca)))
      (load static-key-0 (cat pt-2 ignore-0))
      (stor static-key-0 (cat pt-1 "privkey" b ra-0 serial-b ca))))
  (label 8)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((ca ca) (b b) (a a) (ra ra) (serial-a serial-a)
        (serial-b serial-b) (alpha ra-0) (n n)
        (static-key static-key))))
  (origs (pt-1 (5 3)) (serial-b (3 1)) (serial-a (2 1)) (pt (1 3))
    (n (0 2)))
  (ugens (ra-0 (5 0)) (ra (1 0))))

(comment "Nothing left to do")

(defprotocol dhstatic-state diffie-hellman
  (defrole cert
    (vars (subj ca name) (serial data) (galpha mesg))
    (trace (recv (sig (cert-req subj galpha ca) (privk "sig" subj)))
      (send (sig (cert subj galpha ca serial) (privk "sig" ca))))
    (uniq-orig serial)
    (comment "Certificate Authority"))
  (defrole get-cert
    (vars (self ca name) (serial data) (ra rndx) (static-key locn)
      (ignore mesg))
    (trace
      (send (sig (cert-req self (exp (gen) ra) ca) (privk "sig" self)))
      (recv (sig (cert self (exp (gen) ra) ca serial) (privk "sig" ca)))
      (load static-key ignore)
      (stor static-key (cat "privkey" self ra serial ca)))
    (uniq-gen ra)
    (comment "Get certified"))
  (defrole init
    (vars (a b ca name) (ra rndx) (serial-a serial-b data) (alpha expt)
      (n text) (static-key locn))
    (trace (load static-key (cat "privkey" a ra serial-a ca))
      (recv
        (sig (cert b (exp (gen) alpha) ca serial-b) (privk "sig" ca)))
      (send (enc n a b serial-a serial-b (exp (gen) (mul ra alpha))))
      (recv n))
    (uniq-orig n)
    (gen-st (cat "privkey" a ra serial-a ca))
    (facts (neq a b))
    (comment "Initiator is A"))
  (defrole resp
    (vars (a b ca name) (rb rndx) (serial-b serial-a data) (alpha expt)
      (n text) (static-key locn))
    (trace (load static-key (cat "privkey" b rb serial-b ca))
      (recv
        (sig (cert a (exp (gen) alpha) ca serial-a) (privk "sig" ca)))
      (recv (enc n a b serial-a serial-b (exp (gen) (mul rb alpha))))
      (send n))
    (facts (neq a b))
    (gen-st (cat "privkey" b rb serial-b ca))
    (comment "Responder is B"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule fact-init-neq0
    (forall ((z strd) (b a name))
      (implies
        (and (p "init" z (idx 2)) (p "init" "a" z a) (p "init" "b" z b))
        (fact neq a b))))
  (defgenrule fact-resp-neq0
    (forall ((z strd) (b a name))
      (implies
        (and (p "resp" z (idx 2)) (p "resp" "a" z a) (p "resp" "b" z b))
        (fact neq a b))))
  (defgenrule trRl_get-cert-at-3
    (forall ((z strd))
      (implies (p "get-cert" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_get-cert-at-2
    (forall ((z strd))
      (implies (p "get-cert" z (idx 4)) (trans z (idx 2)))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (a name) (ra rndx) (serial-a data) (ca name))
      (implies
        (and (p "init" z (idx 1)) (p "init" "ca" z ca)
          (p "init" "serial-a" z serial-a) (p "init" "ra" z ra)
          (p "init" "a" z a))
        (gen-st (cat "privkey" a ra serial-a ca)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (b name) (rb rndx) (serial-b data) (ca name))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "ca" z ca)
          (p "resp" "serial-b" z serial-b) (p "resp" "rb" z rb)
          (p "resp" "b" z b))
        (gen-st (cat "privkey" b rb serial-b ca)))))
  (lang (cert-req (tupl 3)) (cert (tupl 4)) (sig sign)))

(defskeleton dhstatic-state
  (vars (serial-b serial-a data) (n text) (ca a b name) (pt pval)
    (static-key locn) (rb rndx) (alpha expt))
  (defstrand resp 4 (serial-b serial-b) (serial-a serial-a) (n n) (a a)
    (b b) (ca ca) (static-key static-key) (rb rb) (alpha alpha))
  (non-orig (privk "sig" ca) (privk "sig" a))
  (traces
    ((load static-key (cat pt "privkey" b rb serial-b ca))
      (recv
        (sig (cert a (exp (gen) alpha) ca serial-a) (privk "sig" ca)))
      (recv (enc n a b serial-a serial-b (exp (gen) (mul rb alpha))))
      (send n)))
  (label 24)
  (unrealized (0 1))
  (origs)
  (comment "Not closed under rules"))

(defskeleton dhstatic-state
  (vars (ignore ignore-0 mesg) (serial-b serial-a data) (n text)
    (a b ca name) (pt pt-0 pt-1 pt-2 pval)
    (static-key static-key-0 locn) (ra ra-0 rndx))
  (defstrand resp 4 (serial-b serial-b) (serial-a serial-a) (n n) (a a)
    (b b) (ca ca) (static-key static-key) (rb ra) (alpha ra-0))
  (defstrand get-cert 4 (ignore ignore) (serial serial-b) (self b)
    (ca ca) (static-key static-key) (ra ra))
  (defstrand cert 2 (galpha (exp (gen) ra)) (serial serial-b) (subj b)
    (ca ca))
  (defstrand cert 2 (galpha (exp (gen) ra-0)) (serial serial-a) (subj a)
    (ca ca))
  (defstrand init 3 (serial-a serial-a) (serial-b serial-b) (n n) (a a)
    (b b) (ca ca) (static-key static-key-0) (ra ra-0) (alpha ra))
  (defstrand get-cert 4 (ignore ignore-0) (serial serial-a) (self a)
    (ca ca) (static-key static-key-0) (ra ra-0))
  (precedes ((1 0) (2 0)) ((1 3) (0 0)) ((2 1) (1 1)) ((2 1) (4 1))
    ((3 1) (0 1)) ((3 1) (5 1)) ((4 2) (0 2)) ((5 0) (3 0))
    ((5 3) (4 0)))
  (non-orig (privk "sig" a) (privk "sig" ca))
  (uniq-orig serial-b serial-a n)
  (uniq-gen ra ra-0)
  (gen-st (cat "privkey" a ra-0 serial-a ca)
    (cat "privkey" b ra serial-b ca))
  (facts (neq b a) (neq a b))
  (leads-to ((1 3) (0 0)) ((5 3) (4 0)))
  (rule fact-resp-neq0 trRl_get-cert-at-2 trRl_get-cert-at-3)
  (operation channel-test (displaced 4 6 get-cert 4)
    (ch-msg static-key-0 (cat pt-1 "privkey" a ra-1 serial-a ca)) (5 0))
  (strand-map 0 1 2 3 5 4)
  (traces
    ((load static-key (cat pt "privkey" b ra serial-b ca))
      (recv
        (sig (cert a (exp (gen) ra-0) ca serial-a) (privk "sig" ca)))
      (recv (enc n a b serial-a serial-b (exp (gen) (mul ra ra-0))))
      (send n))
    ((send (sig (cert-req b (exp (gen) ra) ca) (privk "sig" b)))
      (recv (sig (cert b (exp (gen) ra) ca serial-b) (privk "sig" ca)))
      (load static-key (cat pt-0 ignore))
      (stor static-key (cat pt "privkey" b ra serial-b ca)))
    ((recv (sig (cert-req b (exp (gen) ra) ca) (privk "sig" b)))
      (send (sig (cert b (exp (gen) ra) ca serial-b) (privk "sig" ca))))
    ((recv (sig (cert-req a (exp (gen) ra-0) ca) (privk "sig" a)))
      (send
        (sig (cert a (exp (gen) ra-0) ca serial-a) (privk "sig" ca))))
    ((load static-key-0 (cat pt-1 "privkey" a ra-0 serial-a ca))
      (recv (sig (cert b (exp (gen) ra) ca serial-b) (privk "sig" ca)))
      (send (enc n a b serial-a serial-b (exp (gen) (mul ra ra-0)))))
    ((send (sig (cert-req a (exp (gen) ra-0) ca) (privk "sig" a)))
      (recv
        (sig (cert a (exp (gen) ra-0) ca serial-a) (privk "sig" ca)))
      (load static-key-0 (cat pt-2 ignore-0))
      (stor static-key-0 (cat pt-1 "privkey" a ra-0 serial-a ca))))
  (label 32)
  (parent 24)
  (realized)
  (shape)
  (maps
    ((0)
      ((ca ca) (a a) (b b) (rb ra) (serial-b serial-b)
        (serial-a serial-a) (alpha ra-0) (n n)
        (static-key static-key))))
  (origs (pt-1 (5 3)) (n (4 2)) (serial-a (3 1)) (serial-b (2 1))
    (pt (1 3)))
  (ugens (ra-0 (5 0)) (ra (1 0))))

(comment "Nothing left to do")
