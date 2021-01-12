# CPSA4 Roletran

The Cryptographic Protocol Shapes Analyzer (CPSA) attempts to
enumerate all essentially different executions possible for a
cryptographic protocol.  We call them the shapes of the
protocol. Naturally occurring protocols have only finitely many,
indeed very few shapes.  Authentication and secrecy properties are
easy to determine from them, as are attacks and anomalies.

For each input problem, the CPSA program is given some initial
behavior, and it discovers what shapes are compatible with it.
Normally, the initial behavior is from the point of view of one
participant.  The analysis reveals what the other participants must
have done, given the participant's view.  The search is based on a
high-level algorithm that was claimed to be complete, i.e. every shape
can in fact be found in a finite number of steps.  Further theoretical
work showed classes of executions that are not found by the algorithm,
however it also showed that every omitted execution requires an
unnatural interpretation of a protocol's roles.  Hence the algorithm
is complete relative to natural role semantics.

When we say a role has natural role semantics, we mean that there
exists a program that implements the intent of the specified role.
Until now, establishing the correspondence between a CPSA role and its
implementation has been informal.  It requires a programmer that is
well versed in the semantics of CPSA.  As the messages used in roles
become more complex, the likelihood of errors in the correspondence
increases, even when employing the best programmer/CPSA expert.  The
`cpsa4roletran` compiler automates the translation of a CPSA role into
a language independent procedure.  It uses the same algorithms
implemented in CPSA to ensure a faithful translation.

This document describes the use of the compiler.  It assumes the
reader is experienced with CPSA4, version four of CPSA.  This version
of CPSA is required because channels play an essential part in the
translation.

In typical usage, protocols are analyzed using CPSA4 to ensure they
achieve desired security goals before any attempt is made to construct
programs that implement them.

## Input

`cpsa4roletran` translates an annotated CPSA4 role into a language
independent procedure.  The translator consumes the first protocol
that appears in a CPSA4 input file, and ignores everything else in the
file.  Within the protocol, the translators ignores everything but the
protocol name and the role definitions.

There are two syntactic constraints on roles accepted by `cpsa4roletran`.

 * Every messaging event in the trace of a role must occur on a channel.

 * Every role must include two fields particular to `cpsa4roletran`:
   `inputs` and `outputs`.  The `inputs` specify the terms that become
   the formal parameters of the generated procedure.  The `inputs`
   must include all channel variables that occur in the role's trace.
   The `outputs` contain the terms returned by the generated
   procedure.

The translator ignores all fields in a role definition except its
name, `vars`, `trace`, `uniq-orig`, `inputs`, and `outputs`.

The translator performs various checks to ensure that each role read
is well formed.  It ensures the each term in the inputs is receivable
given previous inputs.  It ensures that any basic value assumed to be
uniquely originating originates in the role's trace, and that no
uniquely originating value is in the inputs.  It ensures that no input
variable is specified as an output.  It also ensures that every
variable in terms that occur in the inputs, outputs, or are assumed to
be uniquely originating also occur in the role's trace.

Finally, a role must be executable.  A role is *executable* iff

 * each transmitted term can be built from the inputs and previously
   sent and received terms;

 * each received term can be destructured into previously seen basic
   values and hashes; and

 * each output term can be build from the inputs and previously sent
   and received terms.

### Input Example

Here is a protocol that performs unilateral authentication.  Its roles
have been annotated for `cpsa4roletran`.

```
(defprotocol unilateral basic
  (defrole init
    (vars (ch chan) (n text) (k akey))
    (trace
     (send ch (enc n k))
     (recv ch n))
    (uniq-orig n)
    (inputs ch k)
    (outputs n))
  (defrole resp
    (vars (ch chan) (n text) (k akey))
    (trace
     (recv ch (enc n k))
     (send ch n))
    (inputs ch (invk k))
    (outputs n)))
```

The initiator role `init` creates a fresh nonce `n` and sends it on
channel `ch` encrypted with public asymmetric key `k`.  To perform the
encryption, the inputs include the key.  The initiator concludes that
it is communicating with a party that possesses the private companion
key by receiving a nonce unencrypted and ensuring it is what it sent.

The responder role `resp` receives the encrypted nonce, and decrypts
with the private key `(invk k)`.  To do the decryption, the inputs
include that key.  In this example, both roles return the nonce for
use by other parts of the program.

## Output

The compiler generates a language independent procedure for each role
in the input protocol.  A user need not understand the details of the
generated code, but a rough understanding can be helpful when the code
generated is unexpected.  It could mean that the CPSA role specifies
something other that what its author intended.

The structure of a generated procedure is:

```
(comment "Role: NAME (FILE_POSITION)")
(defproc NAME (PARAMS) (OUTPUTS) STMTS)
```

where NAME is the name of the role, FILE_POSITION is the location of
the role's definition in the source file, PARAMS are the input
parameters of the procedure, OUTPUTS is the output types of the
procedure, and STMTS is the statements that make up the body of the
procedure.

There are six kinds of statements.

- `(let (VAR TYPE) EXPR)` binds variable VAR to the results of
  expression EXPR.
- `(let (VAR TYPE) (recv CVAR))` binds variable VAR to the results of
  reading a message on channel CVAR.
- `(send CVAR VAR)` transmits the contents of variable VAR on channel
  CVAR.
- `(same VAR1 VAR2)` ensures the contents of VAR1 agrees with what is
  in VAR2.
- `(return VAR ...)` returns the contents of a sequence of variables
  from the procedure.

Finally, there is a comment statement for each message event that
tells where the event being translated occurs in the source file.

Expressions are self explanatory.  They include pairing, projection,
encryption, decryption, hashing, and nonce generation.  The names of
procedures called in expressions include letters that follow the
underscore character which specify type information.  This part of the
procedure name can be safely ignored.

### Init Role Example

The code generated for the `init` role in the unilateral protocol
follows.  Notice how this code agrees with the description of the
role.

```
(comment "Role: init (rtst/unilateral.scm:6:3)")

(defproc init ((p0 chan) (p1 akey)) (text)
  (comment "Send (rtst/unilateral.scm:9:7)")
  (let (v2 text) (nonce_t))
  (let (v3 mesg) (encr_ta v2 p1))
  (send_m p0 v3)
  (comment "Recv (rtst/unilateral.scm:10:7)")
  (let (v4 text) (recv_t p0))
  (same_t v4 v2)
  (return v2))
```

The initiator role `init` creates a fresh nonce `n` (`v2`) and sends
it on channel `ch` (`p0`) encrypted with public asymmetric key `k`
(`p1`).  To perform the encryption, the inputs include the key.  The
initiator concludes that it is communicating with a party that
possesses the private companion key by receiving a nonce unencrypted
(`v4`) and ensuring it is what it sent `(same_t v4 v2)`.
