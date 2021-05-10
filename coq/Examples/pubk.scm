(herald pubk)

(defprotocol pubk basic
  (defrole rho
    (vars (ch chan) (a name) (k akey))
    (trace
     (recv ch (enc a (pubk a) k))
     (send ch (enc a (pubk a))))
    (inputs ch (invk k))))

The new compiler generates:

Definition rho: proc :=
  mkProc
  [(0, Chan); (1, Ikey)]
  [
   (* Recv (pubk.scm:7:6) *)
   Bind (2, Aenc) (Recv_ 0);
   Bind (3, Pair) (Decr_ 2 1);
   Bind (4, Name) (Frst_ 3);
   Bind (5, Akey) (Scnd_ 3);
   Namp 5 4;
   (* Send (pubk.scm:8:6) *)
   Bind (6, Aenc) (Encr_ 4 5);
   Send 0 6;
   Return []
  ].

Notice the name predicate assertion Namp.  It filters out the bad
traces.  Here is its semantics.
