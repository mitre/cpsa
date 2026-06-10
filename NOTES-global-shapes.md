# Experiment: Global Shape Subsumption

Branch: `experiment/global-shape-subsumption` (CPSA 4.4.9).
Status: pivoting to a post-processor design (approach A).  See "APPROACH A
SUBPLAN" below; it supersedes the in-driver subsumption of Substeps 2.2/2.3.

## APPROACH A SUBPLAN — `cpsa4subsume` post-processor (current plan)

### Why this design
Shape determination is inherently a *global* per-problem decision, but the
analyzer streams its output during the search (we want that: progress visibility
and inspectable partial output on abort).  The in-driver attempts (Substeps
2.2/2.3) foundered on this: a subsumed leaf is emitted before its subsumer may be
discovered (the subsumer is NOT always lower-labelled -- confirmed via `attest`,
`sigenc`).  Resolution: keep the analyzer streaming and stock-shaped, and do the
global subsumption as a separate post-processing filter -- idiomatic for CPSA,
which is already a pipeline of tools (`cpsa4shapes`/`cpsa4graph`/`cpsa4sas`/
`cpsa4diff`).  This also keeps the core analyzer essentially untouched, which is
exactly what the upstreaming requirement (HARD REQUIREMENT 2) wants.

Pipeline: `cpsa4 <listener-deletion-only> foo.scm | cpsa4subsume`.
`cpsa4` over-reports shapes (every realized leaf); `cpsa4subsume` rewrites each
subsumed leaf's `(shape)` into `(seen s) (seen-ops (s (subsumption m)))`.

### Step A1 — revert the core analyzer to stock; keep library functions
- **Reduction.hs:** revert FULLY to 4.4.9 stock (remove the `shapes`
  accumulator, the `SeenSkel` sum-type split, the `ReductStable`/completion
  edits, `displaySeen` changes, `homDebugComment`, `subsumptionLog`,
  `globalShapes`).  The driver streams exactly as stock.
- **Displayer.hs:** revert the `displayConj` export add (stock); the tool does not
  need it (it builds the `(subsumption …)` SExpr directly).
- **Strand.hs:** KEEP only:
  - the `useGlobalShapes` flag and its two guarded branches in `generalize` and
    `deleteNodes` that force listener-deletion-only (the Stage-0 change), and
  - the library functions `freshStrdVars`, `skelToConj`, `povSeed`, `injective`,
    `homomorphismExists`, `homomorphismMap` (used by the tool; not wired into the
    search).
  Net core-analyzer delta vs stock: one compile-time flag + two one-line guarded
  branches.  Everything else is library code the tool calls.
- Verify after revert: flag OFF = byte-for-byte stock; flag ON = the Stage-0
  over-report, streamed normally.

### Step A2 — homomorphism API for reloaded skeletons
Skeletons reloaded from `cpsa4` *output* may not carry `prob` (the pov→strand
map; the loader ignores the output-only `(maps …)` field).  So add explicit-prob
variants the tool can call with probs it parses from the output:
- `homomorphismMapWith :: [Sid] -> [Sid] -> Preskel -> Preskel -> Maybe [Sid]`
  (probX probY x y) — uses the given probs in `povSeed`/prefilter.
- `homomorphismMap x y = homomorphismMapWith (prob x) (prob y) x y` (wrapper).
Export the `With` variant.

### Step A3 — `cpsa4subsume` (new: src/CPSA/Subsume/Main.hs + cabal stanza)
Read all SExprs (`readSExprs`).  Partition into problems by splitting at each
`(defprotocol …)` (printed once per problem by `solve`).  Per problem:
- Collect the shape defskeletons (those containing `(shape)`), in order, with
  their SExprs.
- `loadSExprs (defprotocol : shapeSExprs)` → `[Preskel]` (the shapes); zip with
  their SExprs.  (Loader faithfully rebuilds skeletons from output defskeletons —
  already confirmed for `cpsa4cmp`.)
- Parse each shape's `(maps …)` field → its `prob` (pov→strand map), and its
  `(label N)` → output label.
- Subsumption: shape y is subsumed iff some other shape x has
  `homomorphismMapWith (prob x) (prob y) x y = Just _`.  Pick a maximal subsumer
  s (a shape not itself subsumed) and the witnessing map m.
- Rewrite each subsumed y's SExpr: drop the `(shape)` element; add `(seen
  <s-label>)` and `(seen-ops (<s-label> (subsumption m)))`.  Maximal shapes keep
  `(shape)`.
- Emit all SExprs in original order, substituting the rewritten ones.
Reuses the `cpsa4cmp` loading scaffolding.

### Step A4 — validation
Build `cpsa4` (flag ON) and `cpsa4subsume`.  For each protocol:
`cpsa4 foo.scm | cpsa4subsume > patched`, then `cpsa4cmp stock patched`.
Expectation: **123/127 ISOMORPHIC**, with `attest`/`sigenc` restored to MATCH
(global subsumption), and the 4 genuine findings (`nonaug-prune`, `ns-rebinding`,
`wonthull2`, `dh-ca_hack`) remaining.  Spot-check: patched `nonaug-prune` has
skeleton 27 as `(seen 13) (seen-ops (13 (subsumption …)))` and not `(shape)`.

### Risks
- **`(maps)` parsing** (format, multiple entries, prob direction) — the main
  fiddly bit.  Fallback if unreliable: recover `prob` by loading each problem's
  pov skeleton and computing the pov→shape homomorphism directly.
- Per-problem grouping assumes `defprotocol` is emitted once per problem (verify).
- `cpsa4cmp` is kept as the validation tool.

### STATUS — A1, A2, A3 DONE
- **A1:** `Reduction.hs` and `Displayer.hs` reverted to 4.4.9 stock.  `Strand.hs`
  retains only the `useGlobalShapes` flag + two guarded branches (force
  listener-deletion-only) and the library functions.  Verified: flag OFF =
  byte-for-byte stock; flag ON = Stage-0 over-report, streamed pure stock-style
  (no experiment comments).
- **A2:** added `povSeedWith`/`homomorphismMapWith` (explicit pov strand maps);
  `homomorphismMap` is the field-based wrapper; removed dead `povSeed`.
- **A3:** `cpsa4subsume` (`src/CPSA/Subsume/Main.hs` + cabal stanza).  Reads a
  listener-deletion-only run, splits into problems at each `(defprotocol)`, loads
  each problem's shape skeletons via the unmodified `loadSExprs`, recovers `prob`
  from each shape's `(maps)` field, computes global homomorphism subsumption with
  `homomorphismMapWith`, and rewrites each subsumed shape's `(shape)` into
  `(seen s) (seen-ops (s (subsumption m)))`.  Everything else passes through, so
  the full tree is preserved.  Spot check (nonaug-prune): shapes 13 14 28 30 32 36;
  subsumed 27<-13, 35/37/39<-32; skeleton 27 = `(realized)(seen 13)(seen-ops (13
  (subsumption 0 1)))`, not `(shape)` -- matches the earlier in-process global
  computation.

### Suite validation (cpsa4 flag-ON | cpsa4subsume, vs stock via cpsa4cmp)
**123 / 127 ISOMORPHIC**, 0 slow/err.  `attest` and `sigenc` are **restored to
MATCH** (the global post-pass fixes the order-dependence that broke the in-driver
inline approach).  The 4 remaining mismatches are the genuine findings:
- `nonaug-prune` (stock 3, patched 6; stock ⊂ patched), `ns-rebinding` (7 vs 8):
  shapes requiring non-listener strand deletion not reached by forward search.
- `wonthull2` (6 vs 6, 4/6 both ways): the protocol's documented incompleteness /
  deorigination case.
- `dh-ca_hack` (70 vs 69; patched ⊂ stock): one real shape dropped -- still to
  diagnose (DH oracle false-positive or reachability).

Reproduce: `cpsa4 foo.scm | cpsa4subsume > patched; cpsa4cmp stockfile patched`.

---

## (Earlier in-driver design notes follow — superseded by Approach A above.)

## Goal

Replace the bulk of the *generalization* machinery with a more direct procedure
that aligns with the CPSA theory:

- According to the theory, there is a path to any shape that does **not** pass
  through generalization, with the small exception of **listener deletion**
  (which is trivial). The existing generalization code exists only to *locally*
  detect that the homomorphism from the point of view (pov) factors through a
  strictly more general realized skeleton (so the skeleton being generalized
  cannot be a shape).
- The alternative: during search perform **only listener deletion**, then add a
  **global** stage at the end that looks for homomorphisms between the realized
  skeletons at the leaves of the search tree. If there is a homomorphism from
  leaf `x` to leaf `y` (with `x` not isomorphic to `y`), then `y` is **not** a
  shape — `x` is strictly more general. The shapes are the homomorphism-maximal
  (most general) realized leaves.

This is purely experimental. We cannot push to the upstream CPSA repo from here;
changes that prove out will be ported separately by the maintainer.

## HARD REQUIREMENT 1 — everything behind a compile-time flag

Introduce a single new compile-time flag (working name `useGlobalShapes :: Bool`,
default `False`, alongside the existing switches in `Strand.hs` ~lines 185-199).

- **Flag OFF (default): byte-for-byte the current behavior.** We are *adding an
  alternate branch*, not replacing existing code. No existing default path may
  change when the flag is off.
- **Flag ON:** the new global-subsumption path described below.
- The flag must gate *every* behavioral change:
  - `generalize` restricts to listener-only deletion (i.e. behaves as if
    `generalizeOnlyByDeletion && generalizeDeleteOnlyListeners`) only when the
    flag is on. The two existing flags remain independent and untouched.
  - The driver (`Reduction.hs`) collects realized leaves and runs the global
    subsumption post-pass only when the flag is on; otherwise it emits shapes
    inline exactly as today.
- This is *especially* important for Stage 3 (validation): with one binary we
  can diff flag-on output against flag-off output (= stock behavior) per file.

## HARD REQUIREMENT 2 — reviewability for upstreaming

The maintainer can only upstream this if they **completely understand every line**
of new code and every change to existing code. Therefore:

- **Each stage below (except Stage 0, which is a trivial flag flip) must begin by
  writing a short SUBPLAN for that stage alone** — the exact functions to add,
  the exact existing functions to touch, the data flow, and the expected diff
  against stock — before any code is written.
- **Every new function and every change to existing code must be explained
  clearly**: its purpose, its mechanism, why it is correct, and how it is gated
  by the flag. Favor small, self-contained, well-commented additions over edits
  woven into existing functions.
- Prefer additive code (new functions, new flag-guarded branches) over in-place
  rewrites, so the stock path is visibly preserved.

## Design (flag ON)

### Piece 1 — listener-only generalization (reuses existing flags' behavior)
When `useGlobalShapes` is on, `generalize` produces only listener deletions.
`maximize`/`specialization` continue to run (restricted to listener deletion),
so the search's `Stable` leaves are the **listener-minimal realized skeletons** —
already the right candidates for global subsumption. No new listener code.
These leaves *over-report* relative to current shapes (the removed
weaken/forget/separate/non-listener-delete no longer merges them); the global
subsumption performs that merge, more directly and globally.

### Piece 2 — `homomorphismExists x y` via satisfaction + pov-seed
The global pass needs to decide whether a homomorphism `x -> y` exists for
arbitrary realized leaves. Equivalent (per the rule-application analogy) to:
represent `x` as a conjunction of formulas `phi_x`, then check whether `phi_x` is
satisfiable in `y` (i.e. the goal `phi_x => false` is violated by `y`).

```
phi_x   = skelToConj x                 -- [AForm] describing x's content
env0    = seed from prob_x, prob_y     -- bind x's pov-strand vars to matching y-strands
exists  = not (null (conjoin phi_x y (gen0, env0)))
```

- `skelToConj :: Preskel -> [AForm]` is the one real construction task. Build the
  atomic formulas describing `x`: role-length (`Length`), parameters (`Param`),
  orderings (`Prec`), `Non`/`Pnon`/`Uniq`/`UniqAt`/`Ugen`/`UgenAt`/`GenStV`,
  absence, `LeadsTo`, facts (`AFact`). Blueprint: `SAS.hs`
  (`lengthForm`/`paramForm`/`precForm`/`leadsToForm`/`uniqAtForm`/`factForm`),
  which builds the same description but as `SExpr ()` for display — we need the
  `AForm` version (constructors in `Protocol.hs:675`; `Conj = [(Pos,AForm)]`).
- **pov-seed (the key shortcut):** each leaf carries `prob :: [Sid]`, the pov->
  skeleton strand map. For each pov-strand `s`, `x`-strand `prob_x!!s` must map to
  `y`-strand `prob_y!!s`. Pre-bind those strand variables in `env0`, pinning the
  homomorphism on all pov-image strands; only augmented (non-pov) strands remain
  for the search. Analogous to how `checkPOV`/`refines` compose `prob` today.
- **Reuse, not reinvention:** `conjoin :: [AForm] -> Sem` /
  `satisfy` (`Strand.hs:3252`, `Sem = Preskel -> (Gen,Env) -> [(Gen,Env)]`) is
  the rule/goal antecedent-satisfaction engine. Calling it gives us all its
  shortcuts for free: incremental env threading, per-atom role/length pruning,
  and the `geq` term-matching. Sanity invariant: `homomorphismExists x x == True`.

### Piece 3 — collect leaves + global subsumption (Reduction.hs)
The `ReductStable` case in `step` currently writes a `Shape`. When the flag is on,
**accumulate** the leaf instead (an `IORef [LPreskel]` is the least-invasive
mechanism — the driver is already in IO). At per-problem completion
(`breadth ... [] []`, "Nothing left to do"), keep leaf `y` iff no other
non-isomorphic leaf `x` has `homomorphismExists x y`; emit the survivors (the
homomorphism-maximal antichain) as shapes. When the flag is off, this path is
untouched.

## Confirmed building blocks (code references, CPSA 4.4.9)

| Item | Location |
|------|----------|
| `data AForm` (skeleton-content predicates) | `Protocol.hs:675` |
| `type Conj = [(Pos, AForm)]` | `Protocol.hs:708` |
| `conjoin`/`satisfy`, `type Sem` | `Strand.hs:3250-3262` |
| `homomorphism k k' mapping` (validator w/ known map) | `Strand.hs:2352` |
| `isomorphic`, `findIsomorphisms`, `permutations` | `Strand.hs:1234-1262` |
| `prob` (pov->skel strand map) | `Strand.hs:575` |
| `composeStrandMap` | `Strand.hs`/`Cohort.hs` |
| existing switches (`generalizeOnlyByDeletion`, `generalizeDeleteOnlyListeners`, `omitGeneralization`) | `Strand.hs:190-199`, `Cohort.hs:126` |
| `reduce`/`reduceNoTest`/`maximize` shape determination | `Cohort.hs:351-373` |
| driver: `solve`/`begin`/`search`/`mode`/`breadth`/`step`; `ReductStable`->Shape | `Reduction.hs:227-338` |
| skeleton-as-formula blueprint (display SExpr) | `SAS/SAS.hs:748-815` |

## New vs reused
- **New:** `useGlobalShapes` flag; `skelToConj`; pov-seed env builder;
  `homomorphismExists` wrapper; `Reduction.hs` collect + post-pass (flag-guarded);
  flag-guarded listener-only branch in `generalize`.
- **Reused unchanged:** `conjoin`/`satisfy`, `geq`, `homomorphism`, `prob`/
  `composeStrandMap`, search/cohort/listener-deletion path, isomorphism checks.

## Risks to watch
- **`skelToConj` fidelity:** `phi_x` must capture x's content *exactly* so that
  satisfaction <=> homomorphism (no under-/over-constraining). SAS is the
  checklist; verify all of length/param/prec/non/pnon/uniq/uniq-at/ugen/gen-st/
  absence/leads-to/facts are represented.
- **Env-seed semantics:** must bind the same strand variables `satisfy`/`Length`
  expects; a mismatch silently breaks it. Sanity-test `homomorphismExists x x`.
- **Cost:** O(leaves^2) `conjoin` calls; pre-filter with cheap `gist`/strand-count
  /skyline checks before the full check.
- **Theory completeness:** the empirical test is `cpsa4diff` of flag-on shapes vs
  stock (flag-off / 4.4.9) across the suite.

## Incremental rollout (each step independently checkable)

- **Stage 0 (trivial — no subplan needed):** add the `useGlobalShapes` flag
  (default off) and the flag-guarded listener-only branch in `generalize`. With
  the flag on, build, run the suite, and `cpsa4diff` vs stock to measure the
  over-reporting baseline (how much the leaves differ before subsumption).
- **Stage 1 (SUBPLAN FIRST):** implement `skelToConj` + pov-seeded
  `homomorphismExists`. Unit-check: `x x` true; a known general->specific pair
  true, the reverse false.
- **Stage 2 (SUBPLAN FIRST):** wire collect + global subsumption into
  `Reduction.hs`, flag-guarded.
- **Stage 3 (SUBPLAN FIRST):** `cpsa4diff` flag-on shapes vs stock 4.4.9 across
  the suite; close `skelToConj` gaps until they match. The flag makes this a
  same-binary A/B.
- **Stage 4 (SUBPLAN FIRST):** measure performance — does dropping generalization
  beat the O(leaves^2) subsumption cost, net?

## Validation harness
Build the branch with `cabal build exe:cpsa4 --allow-newer`; compare flag-on vs
flag-off (or vs stock 4.4.9) per file with `cpsa4diff`. The `perftst` tool (with
staged stock references) can drive the suite-wide comparison.

## Stage 0 results (flag ON: listener-only generalization, NO subsumption yet)

Shape counts (count of `(shape)` markers) vs stock 4.4.9:

| protocol | stock | flag-ON | delta | cpsa4diff |
|----------|-------|---------|-------|-----------|
| ns       | 10    | 11      | +1    | DIFFER |
| yahalom  | 2     | 8       | +6    | DIFFER |
| envelope | 10    | 10      | 0     | MATCH  |
| blanchet | 8     | 8       | 0     | MATCH  |
| woolam   | 12    | 12      | 0     | MATCH  |
| nsl3     | 3     | 8       | +5    | DIFFER |

(NOTE: count `(shape)` markers, NOT `(defskeleton` — the latter counts every
skeleton in the derivation tree, not the shapes.)

Observations:
- flag-ON OVER-reports shapes, as expected: with generalization restricted to
  listener deletion and no subsumption yet, the forward search reports extra,
  more-specific realized leaves as shapes that stock merges via generalization.
- envelope/blanchet/woolam already MATCH: forward search + listener deletion
  alone gives the right shapes there.
- ns/yahalom/nsl3 over-report; the Stage 2 global subsumption pass (which only
  removes subsumed leaves) is exactly what should merge these down.

## Stage 1 SUBPLAN — `skelToConj` + pov-seeded `homomorphismExists`

Scope: **pure, additive code only.** No flag-guarded behavior changes to the
search/driver in this stage (that is Stage 2). Everything here is new top-level
functions in `Strand.hs`, exercised by a temporary test harness, so the flag-off
and flag-on *binaries* behave exactly as in Stage 0. Net effect on stock paths:
**zero** (the new functions are not yet called from anywhere on the live path).

### What a homomorphism is, operationally
A homomorphism `x -> y` is a map from `x`'s strands/variables to `y`'s
strands/terms that preserves all of `x`'s structure (role lengths, parameters,
orderings, origination/freshness assumptions, facts, etc.). The satisfaction
engine already decides exactly this: if we describe `x`'s content as a list of
atomic formulas `phi_x` (variables = `x`'s strand/term variables) and then run
`conjoin phi_x y` against the *target* skeleton `y`, every successful
`(Gen,Env)` result is precisely a structure-preserving map `x -> y`. So:

```
homomorphismExists x y  ==  not (null (conjoin (skelToConj x) y seed))
```

This is the same mechanism rule/goal antecedents use (`conjoin (antec g) k ...`),
reused unchanged.

### Function 1 / SUBSTEP 1 — `skelToConj` (REFINED)

#### Corrected foundation (supersedes the earlier SAS-mirror sketch)
The first sketch assumed `skelToConj` could reuse SAS's `skel` accessors. It
**cannot**: `SAS.hs` defines its *own* local `Preskel` type (`SAS/SAS.hs:238`),
a parse-back of *displayed* output, whose fields (`nons`/`pnons`/`origs`/
`genNodes`/`leadsTos`/`varmap`, strands as *variables*) are **not** the live
`Strand.hs` `Preskel`. In the live `Preskel` strands are integer `Sid`s,
instances carry an `Env`, and content lives in fields `knon`/`kpnon`/`kunique`/
`korig`/`kuniqgen`/`kugen`/`kgenSt`/`kconf`/`kauth`/`kfacts`/`orderings`. So
`skelToConj` extracts directly from the live `Preskel`. There is **no** existing
live `Preskel -> [AForm]` converter to reuse (only the reverse,
`Characteristic.characteristic :: Conj -> Preskel`, and SAS's display-only form),
so this function is genuinely new.

Two authoritative references fix the encoding exactly:
- **`LoadFormulas.hs`** (the parser, lines ~286-446) — the *inverse*; it pins the
  exact term encoding each `AForm` constructor expects.
- **`Displayer.displayRest`** (`Displayer.hs:262`) — shows which live field feeds
  each displayed clause.

#### Proposed signature
```haskell
skelToConj :: Gen -> Preskel -> (Gen, [Term], [AForm])
```
- Takes a `Gen` so the caller can thread freshness against the target `y` later.
- Returns: advanced `Gen`; `strandVars` indexed by `Sid` (`strandVars !! s` is the
  fresh `strd` variable standing for strand `s`); and the conjunction `phi_x`.

**Why mint fresh strand variables.** `AForm`s reference strands by a *term*; the
live skeleton uses `Sid`. Encoding strand `s` as the constant `Z s` would force
`y` to literally contain strand `s` (identity, not homomorphism). Instead mint one
fresh `strd` variable per strand (`newVarDefault g "z" "strd"`) so strands form
the variable *domain* of the homomorphism. A node `(s,i)` becomes the `NodeTerm
(strandVars !! s, indxOfInt i)` where `indxOfInt = Y` (`Algebra.hs:2432`).

**Message variables.** `phi_x` uses `x`'s own message variables (`kvars x`)
directly — they are already the right pattern variables, and matching binds them
to `y`'s terms. Cross-skeleton id-collision/freshening (possible when `x` and `y`
share *ancestor* variables, since gens are monotonic but ancestors are inherited)
is a **wrapper** concern handled when conjoining against `y`, not here.

#### Per-constructor extraction (live source -> `AForm`; encoding per the parser)

| `AForm` | Live source | Encoding |
|---|---|---|
| `Length` | each non-listener `inst` at strand `s` | `Length (role inst) (sv!!s) (indxOfInt (height inst))` |
| (listener) | strand `s` with `listenerTerm inst = Just t` | `Length (listenerRole prot) (sv!!s) (indxOfInt 2)` + `Param (listenerRole) x 2 (sv!!s) t` (mirror `loadListener`, `LoadFormulas.hs:300`) |
| `Param` | `sansPtMaplets (reify (rvars r) (env inst))` per strand `s` | for `(v,t)` with `firstOccurs v r = Just i` => `Param r v (i+1) (sv!!s) t` |
| `Prec` | `orderings k` | `Prec (sv!!s, Y i) (sv!!s', Y i')` |
| `Non` | `sansPts (knon k)` | `Non t` |
| `Pnon` | `sansPts (kpnon k)` | `Pnon t` |
| `UniqAt` | `korig k` entries with origin node(s) | `UniqAt t (sv!!s, Y i)` (one per node) |
| `Uniq` | uniques with no origin node in `k` | `Uniq t` |
| `UgenAt` | `kugen k` entries with gen node(s) | `UgenAt t (sv!!s, Y i)` (one per node) |
| `Ugen` | uniqgens with no gen node | `Ugen t` |
| `GenStV` | `kgenSt k` | `GenStV t` |
| `LeadsTo` | `nodePairsOfSkel k` (`Strand.hs:3335`, node-indexed) | `LeadsTo (sv!!s, Y i) (sv!!s', Y i')` |
| `Conf` | `kconf k` | `Conf t` |
| `Auth` | `kauth k` | `Auth t` |
| `AFact` | `kfacts k`, skipping `"trans"` | `AFact name (map ftermToTerm fs)`; `FSid s -> sv!!s`, `FTerm t -> t` |

Helpers confirmed: `indxOfInt i = Y i` (`Algebra.hs:2432`); `firstOccurs v r =
firstOccursAt v (rtrace r)` (`Protocol.hs:448`); `reify :: [Term] -> Env ->
[(Term,Term)]` (`Algebra.hs:2346`); `strdMatch t p = match t (Z p)` /
`strdLookup` (`Algebra.hs:2399-2406`); `displayConj :: Context -> [AForm] ->
SExpr ()` (`Displayer.hs:88`, for the verification harness).

#### Deliberately NOT emitted (flagged)
- **`absent` (`kabsent`)** — no `AForm` constructor; SAS omits it too; absence is
  enforced structurally by the term algebra during matching. This is adjacent to
  the injectivity worry (below). Revisit if unit tests fail on an `absent`-bearing
  skeleton (candidate: a guard, or `Equals`/`Component` encoding).
- **`precur` (`kprecur`)** — no direct `AForm`; needs investigation as to whether
  it constrains homomorphism existence. Flagged.
- **`priority`/`operation`/`rule`/`traces`** — display/bookkeeping, not semantic
  content. Skipped.

#### Injectivity-on-strands (carried to the wrapper, not expressible here)
A homomorphism must be **injective on strands**, but an `AForm` *conjunction* can
only assert positive facts — there is no "strand /= strand" conjunct, and
`absent`/`Equals` give no inequality. So injectivity cannot be forced inside
`skelToConj`/satisfaction; satisfaction could otherwise collapse two `x`-strands
onto one `y`-strand. The clean fix lives in the **wrapper** (`homomorphismExists`,
a later substep): since `skelToConj` returns `strandVars`, the wrapper reads back
`strdLookup env (sv!!s)` for every strand in each result `Env` and **keeps only
Envs whose strand map is injective**. `skelToConj`'s sole obligation toward this
is to return `strandVars`.

#### Open questions to settle before/while coding
1. **Origination multiplicity** — emit one `UniqAt`/`UgenAt` per node in the
   `korig`/`kugen` node list; confirm against SAS `origs`/`genNodes` handling.
2. **`noOrigUniqs`/`noGenUniqs` live computation** — a unique absent from `korig`
   (no node) => `Uniq`; otherwise `UniqAt`. Same split for uniqgens via `kugen`.
3. **Facts referencing strands (`FSid`)** map to `sv!!s` (not `Z s`) to stay
   homomorphic — confirm `AFact` term-sort expectations.
4. **`absent`/`precur`** necessity — deferred to the unit tests, kept visible.

#### Substep-1 isolation tests (no live-path impact)
- Temporary harness: on a real run, take a few realized skeletons, call
  `skelToConj`, render via `displayConj`, eyeball against SAS's formula output for
  the same skeletons (match modulo variable names + the known omissions).
- Invariant: `foldl aFreeVars [] phi_x` is a subset of `strandVars ++ kvars k`
  (no dangling variables).
- Clean build with the new (unused) function exported; both flag-off and flag-on
  binaries remain byte-for-byte Stage 0.

### Function 2 — `povSeed :: Preskel -> Preskel -> (Gen, Env)`
Builds the seed `(Gen,Env)` that pins the homomorphism on all pov-image strands,
the "shortcut" the rule code analogue suggests.

  - Both `x` and `y` descend from the same pov, so `prob :: [Sid]` (`Strand.hs:585`)
    is indexed by pov-strand: `prob x !! s` is `x`'s image of pov-strand `s`, and
    `prob y !! s` is `y`'s image. (Both leaves carry a `prob` of the same length —
    the pov strand count.)
  - For each pov-strand `s`, bind `x`'s strand variable for `prob x !! s` to `y`'s
    concrete strand index `prob y !! s`:
    `env <- strdMatch (kstrands x !! (prob x !! s)) (prob y !! s) (g, e)`
    (`strdMatch t p` = `match t (Z p)`, `Algebra.hs:2399`).
  - Once seeded, `glength`/`gparam`/`gprec` see `strdLookup e z = Just s` and
    short-circuit to that fixed `y`-strand instead of searching all strands
    (`Strand.hs:3413,3430`) — exactly the pinning we want. Only non-pov
    (augmented) strands remain free for the engine to map.

  - **Gen / variable-freshness (central correctness point).** `phi_x`'s variables
    live in `x`'s gen space; `y`'s terms live in `y`'s. If ids collide, `match`
    could wrongly identify an `x` pattern var with an unrelated `y` var. Safe
    default: **freshen `phi_x` (and `kstrands x`) against `gen y`** before
    conjoining — clone `x`'s variables into fresh ids above `gen y`'s counter
    (using the same `newVarDefault`/clone machinery skeletons already use), and
    build `povSeed`/`phi_x` over the freshened variables. The returned `Gen` is
    the advanced counter. The two unit tests below are precisely what catches a
    freshening mistake.

### Function 3 — `homomorphismExists :: Preskel -> Preskel -> Bool`
The wrapper:
```
homomorphismExists x y =
  let (phi_x', seed) = ...freshen x against gen y, build phi_x' and povSeed...
  in not (null (conjoin phi_x' y seed))
```
Optionally short-circuit obvious non-maps first with cheap checks (strand count,
per-role length multiset, #orderings) before the full `conjoin` — deferred to
Stage 2 where cost matters; Stage 1 keeps it simple and correct.

### Files touched
- `src/CPSA/Strand.hs`: **add** `skelToConj`, `povSeed`, `homomorphismExists`
  (and any small freshening helper). Export them. **No edits to existing
  functions.** No flag references in this stage.

### Unit checks (acceptance for Stage 1)
A temporary `Main`-level or GHCi harness (not committed to the live path):
1. **Reflexivity:** for every realized leaf `x` in a run, `homomorphismExists x x
   == True`. (Catches `skelToConj`/seed/freshening errors.)
2. **General→specific directionality:** take a known pair where stock
   generalization merged `y` into more-general `x`; assert
   `homomorphismExists x y == True` and `homomorphismExists y x == False`
   (unless isomorphic). Good source: a `ns`/`yahalom` leaf pair from the Stage 0
   over-reporting set.
3. **Spot-check vs `homomorphism` validator** (`Strand.hs:2352`): where a concrete
   mapping is known, the engine's success set should be consistent with the
   existing validator.

### Expected diff against stock
None in binary behavior (functions unused on the live path). The only artifacts
are the three unit-check results, recorded here before proceeding to Stage 2.

## SUBSTEP 1 STATUS — DONE (skelToConj)

`skelToConj :: Gen -> Preskel -> (Gen, [Term], [AForm])` implemented in
`Strand.hs` (exported), with the exact extraction described above.  Validated via
a flag-gated debug emit in `Reduction.hs` (`skelConjComment`, gated by
`useGlobalShapes`): each emitted shape is followed by a `(comment skelToConj ...)`
rendering of its conjunction (`displayConj`).  Ran ns / yahalom / envelope / nsl3
/ dhstatic-state with the flag ON; one rendering per shape, field-for-field
matching the shape display across **all** AForm paths — lengths, params (incl. DH
`exp`/`mul`/`gen` terms), prec, non, uniq/uniq-at, ugen-at, gen-st, leads-to
(computed via `nodePairsOfSkel`, which is correct since leads-to is a display-time
relation, not stored), and facts.  No conf/auth in the sample protocols.  The
flag is currently left ON for inspection; revert to `False` before any commit.

The debug emit (`skelConjComment` + its call site) is intentionally lightweight
and flag-gated; it stays through Stage 2 (useful) and can be removed later.

---

## Stage 2 SUBPLAN — collect leaves + global homomorphism subsumption

Goal: with the flag ON, stop emitting realized leaves inline as shapes; instead
**accumulate** them per problem and, at problem completion, emit only the
homomorphism-maximal (most general) leaves as shapes.  This is the removal pass
that collapses the Stage-0 over-reporting down to the true shape set.  Flag OFF:
byte-for-byte stock behavior (no accumulation, inline shape emit as today).

Stage 2 has three substeps, each independently checkable; per HARD REQUIREMENT 2
every new function and every edit to existing code is explained.  **Substep 2.1
(the homomorphism oracle) is the deferred second half of Stage 1** — it must land
and pass its unit checks before the driver wiring (2.2/2.3) is trusted.

### Key discoveries that shape this design (verified in 4.4.9 source)
- **One accumulation hook.** In normal mode, every realized *shape* leaf flows
  through the `ReductStable` case (`Reduction.hs:331`, emit at :352).  The other
  `Shape` emits fire only under `optGoalsSat` / `optDepth` / `fast`
  (`--no-isochk`) modes.  We therefore accumulate at `ReductStable` only and
  declare those alternate modes **out of scope / unsupported** when the flag is
  ON (documented; the breadth path is the supported one).
- **`gmerge (gen x) (gen y)`** (`Algebra.hs:240`, as used by `findReplacement`,
  `Strand.hs:2402`) yields a combined `Gen` above both skeletons' variables.  This
  is the clean answer to the cross-skeleton variable-collision worry from Stage 1
  — no manual "freshen/clone x" step is needed.  (Pattern/target id overlap is
  harmless: `match` binds x-domain vars to y-range terms; mapping `x.n` to `y.n`
  is a legitimate homomorphism.  `gmerge` only guarantees freshly *created*
  variables — e.g. in `bldInstance` inside `gparam` — collide with neither.)
- **An existing complete validator.** `homomorphism :: Preskel -> Preskel ->
  [Sid] -> [(Gen,Env)]` (`Strand.hs:2363`) = `findReplacement` (strand-by-strand
  trace match under a *given* full strand mapping, `gmerge`d gen) + `validateEnv`
  (checks non/pnon/unique/uniqgen/**absent**/auth/conf/genSt/origination/orderings
  preserved).  It is **currently unused** in 4.4.9, so it is available as an
  oracle, but is itself unexercised — hence we use it to *validate* candidates,
  not as the sole search.  Its `mapping` is indexed by x-strand: `mapping !! s` is
  the y-strand that x-strand `s` maps to.
- **Functional accumulator.** The driver already threads list accumulators
  (`todo`, `toobig`) through `breadth`/`step`.  We add one more, `shapes ::
  [LPreskel]`, in the same style — no `IORef`, cleaner than the original note's
  suggestion.

### Substep 2.1 — the homomorphism oracle (deferred Stage-1 substep 2)
New, pure functions in `Strand.hs` (additive; no edits to existing functions):

1. `povSeed :: Gen -> Preskel -> [Term] -> Preskel -> [(Gen, Env)]`
   Given the `gmerge`d gen, the source `x` with its `strandVars` (from
   `skelToConj`), and the target `y`, build the seed env that pins the
   pov-image strands.  For each pov-strand index `s` (`0 .. length (prob x) - 1`):
   bind `strandVars !! (prob x !! s)` to the concrete y-strand `prob y !! s` via
   `strdMatch` (`Algebra.hs:2399`).  Returns the seeded `(gen, env)` (a singleton
   list, or `[]` if the prob lengths disagree — different pov, never compared).
   Rationale: `glength`/`gparam`/`gprec` short-circuit on `strdLookup`, so seeded
   strands are pinned and only augmented x-strands are searched.

2. `homomorphismExists :: Preskel -> Preskel -> Bool`
   Decide whether a (strand-injective) homomorphism `x -> y` respecting the pov
   exists.  Recommended **search-then-validate** design (uses the conjoin search
   the user asked for, and the existing validator for correctness):
   ```
   homomorphismExists x y =
     prefilter x y &&                              -- cheap necessary conditions
     let g0            = gmerge (gen x) (gen y)
         (g1, sv, phi) = skelToConj g0 x           -- reuse Substep 1
         seeds         = povSeed g1 x sv y
     in any viable
          [ env | (_, env) <- conjoin phi y =<< seeds ]   -- search mappings
     where
       viable env =
         let m = [ strdLookup env (sv !! s) | s <- strandids x ] in
         all isJust m && injective (catMaybes m) &&        -- strand-injective
         not (null (homomorphism x y (catMaybes m)))       -- full validate
   ```
   - `conjoin phi y seed` searches assignments for augmented strands and binds
     message vars; each result `env` proposes a strand mapping (read back via
     `strdLookup` on `sv`).
   - **Injectivity** (the user's concern) is enforced here, not in `skelToConj`:
     reject any `env` whose strand map repeats a y-strand.  A conjunction cannot
     express strand inequality, so filtering the results is the mechanism.
   - **Re-validation via `homomorphism x y m`** runs the complete `validateEnv`
     (origination, orderings, **absent** — which `skelToConj` deliberately omits),
     closing the fidelity gap of the pure-conjoin path.  If profiling later shows
     this is redundant, it can be dropped, but it is the conservative default and
     keeps the amount of *trusted-new* logic minimal.
   - `prefilter x y`: `nstrands x <= nstrands y`, per-role strand-count multiset of
     x dominated by y's, `length (prob x) == length (prob y)`.  Cheap rejects
     before any `conjoin`.

   Files touched: `Strand.hs` add `povSeed`, `homomorphismExists`, small helpers
   (`injective`); export `homomorphismExists`.  No edits to existing functions.

   Acceptance (the deferred Stage-1 unit checks, run via the flag-gated harness):
   - **Reflexivity:** `homomorphismExists x x == True` for every realized leaf.
   - **Directionality:** for a Stage-0 over-report pair where stock merged `y`
     into more-general `x`: `homomorphismExists x y == True`,
     `homomorphismExists y x == False`.
   - **Oracle agreement:** when `conjoin` proposes mapping `m`, `homomorphism x y
     m` is non-empty (search and validator agree).

#### SUBSTEP 2.1 STATUS — DONE (oracle implemented + validated)
Implemented in `Strand.hs` (exported `homomorphismExists`; helpers `povSeed`,
`injective`).  Design as planned: `gmerge` gens, `skelToConj` + `povSeed` +
`conjoin` to search strand maps, then keep maps that are total + injective +
confirmed by the existing `homomorphism` validator.

Tested via a flag-gated harness in `Reduction.hs`: a `shapes :: [LPreskel]`
accumulator threaded through `breadth`/`step` (behavior-preserving — leaves still
emit inline this substep), collecting realized leaves per problem; at completion
`homDebugComment` runs the oracle over them and emits
`(comment global-shapes-debug (leaves ..) (reflexive ..) (maps ..) (survivors ..)
(counts ..))`.

Results (flag ON), survivors = homomorphism-maximal leaves:

| proto | stock | leaves | survivors | reflexive | result |
|-------|-------|--------|-----------|-----------|--------|
| ns       | 10 | 11 | 10 | all | MATCH |
| yahalom  | 2  | 8  | 2  | all | MATCH |
| nsl3     | 3  | 8  | 3  | all | MATCH |
| envelope | 10 | 10 | 10 | all | MATCH |
| blanchet | 8  | 8  | 8  | all | MATCH |
| woolam   | 12 | 12 | 12 | all | MATCH |
| dhstatic-state | 2 | 2 | 2 | all | MATCH (stateful: absent/gen-st/leads-to) |

- **Reflexivity** (`homomorphismExists x x`) holds for every leaf in every block.
- **Survivor counts equal stock shape counts in all cases** — the Stage-0
  over-reports (ns +1, yahalom +6, nsl3 +5) collapse exactly.  This already
  previews the Stage-2.4 result; Stage 3 still must confirm the surviving shapes
  are iso to stock's, not merely equinumerous.
- **Maps are transitive/sensible** (e.g. yahalom: leaf 8 dominates all 6 others,
  16 dominates its specializations) — a proper generality hierarchy.
- The stateful `dhstatic-state` runs without error, exercising the `absent`
  checking that lives in `validateEnv` (the reason for search-then-validate).

Files touched: `Strand.hs` (+`povSeed`,`homomorphismExists`,`injective`; export);
`Reduction.hs` (+`shapes` accumulator threaded; +`homDebugComment` harness).  No
existing-function logic changed; flag OFF remains byte-for-byte stock.

### Substep 2.2 — collect realized leaves (driver wiring, flag-gated)
Thread a `shapes :: [LPreskel]` accumulator through `breadth` and `step`,
mirroring `todo`/`toobig`:
- `mode` (`Reduction.hs:299`) calls `breadth ... todo [] []` — initialize `shapes`
  to `[]` (one extra `[]` argument).
- `breadth`/`step` signatures gain a `shapes` parameter, passed through unchanged
  on every recursive call.
- **`ReductStable` (`:331`)**: when `useGlobalShapes` is ON, **accumulate**
  `lk` into `shapes` and emit nothing (the leaf's shapehood is decided globally).
  When OFF, behave exactly as today (`wrt ... Shape`).  The existing `recall
  ... seen` dedup is preserved, so accumulated leaves are pairwise non-isomorphic.
  The Stage-1 `skelConjComment` debug emit is subsumed/removed here.
- All non-`ReductStable` emit sites are unchanged.

Check: with the flag ON, build and confirm output is unchanged except that the
inline `(shape)` markers disappear (they move to the post-pass) — i.e. the tree
still prints, shapes are pending.

#### SUBSTEP 2.2 STATUS — DONE (defer inline leaf emission)
Single behavioral change in `Reduction.hs` `ReductStable`: when `useGlobalShapes`
is ON, an unseen realized leaf is **accumulated only** (no inline `(shape)`
emission); when OFF, it emits the shape inline exactly as stock.  The accumulator
threading (from 2.1) is unchanged.  The now-dead substep-1 helper `skelConjComment`
was removed (clean build, no warnings).

Checkpoint verified:
- Flag ON, `ns`: `(shape)` markers = **0** (deferred), `(defskeleton` = 22 (tree
  still prints fully), 9 `global-shapes-debug` blocks with survivors summing to 10
  (= stock).  Shapes are pending the 2.3 post-pass.
- Flag OFF, `ns`: rebuilt and confirmed **byte-for-byte stock** — `(shape)` = 10
  inline, zero debug blocks.  The invariant "flag OFF = stock" holds.

(Intermediate state by design: with the flag ON the binary currently emits no
`(shape)` at all; Substep 2.3 adds the post-pass that emits the survivors.)

### Substep 2.3 — global subsumption post-pass + emit survivors (flag-gated)
At per-problem completion `breadth p h ks _ n _ [] [] shapes` (`Reduction.hs:307`,
the "Nothing left to do" point):
- When OFF: unchanged (`shapes` is always `[]`).
- When ON: compute the homomorphism-maximal antichain and emit survivors:
  ```
  let survivors = [ y | y <- shapes
                      , not (any (\x -> label x /= label y &&
                                        homomorphismExists (content x) (content y))
                                 shapes) ]
  mapM_ (\lk -> wrt p h (commentPreskel lk [] [] Shape Nada "global-shape")) survivors
  ```
  `y` is a shape iff no *other* accumulated leaf `x` maps homomorphically onto it
  (i.e. `x` is strictly more general; non-iso is guaranteed by the `seen` dedup,
  so the two-way case collapses to iso and cannot occur here).  Survivors are
  emitted as proper `(defskeleton ... (shape))`, so `(shape)`-marker counting
  works exactly as in Stage 0 validation.
- Complexity O(n²) `homomorphismExists` calls per problem, knocked down by
  `prefilter`.  `n` = realized-leaf count (small after dedup).

#### SUBSTEP 2.3 REDESIGN — non-destructive (keep leaves, log subsumption)
The first 2.3 (defer leaves, emit only survivors) had a **bookkeeping bug**: it
removed the realized non-shape leaves from the output, so their unrealized parents
dangled (e.g. nonaug-prune skeleton 21; wonthull2 skeletons 10, 13 appeared as
childless leaves) and many legitimate realized children simply vanished.

Fix (per request): **keep every realized leaf in the output** exactly as stock
emits it (it is a legitimate child of its parent), and record the subsumption
**non-destructively**.  Concretely:
- `ReductStable` now **always emits the realized leaf inline** (both flag states);
  when the flag is ON it *additionally* accumulates the leaf.  Nothing is removed,
  so the tree is whole again (ns: 33 defskeletons = stock; nonaug-prune: skeleton
  21 regains its child).
- At problem completion, when the flag is ON, emit one summary comment
  `subsumptionLog`:
  ```
  (comment global-shape-subsumption
    (subsumed <y> (by <s>))   ; for each non-shape realized leaf y, a shape s
    ...                       ; (s maps homomorphically onto y); one s suffices
    (shapes <z> ...))         ; the homomorphism-maximal leaves
  ```
  Direction is per-leaf: each non-shape leaf points to a **shape that subsumes
  it** (not the other way round).
- Inline `(shape)` markers now stay on **all** realized leaves (the forward-search
  over-report); the *true* shapes are the `(shapes ...)` list in the log.  So
  shape validation must compare against the log's `(shapes ...)`, not raw inline
  `(shape)` counts (a follow-up for `cpsa4cmp`/validation tooling).
- Flag OFF rebuilt and confirmed **identical** to the stock baseline.

Spot checks (flag ON): ns — 33 defskeletons, log shapes total 10 (one
`(subsumed 24 (by 22))`), = stock 10.  nonaug-prune — tree whole, log shapes
`13 14 28 30 32 36` (6) with `27←13, 35/37/39←32`; still 6 vs stock 3 (the
genuine non-listener-strand-deletion finding, unchanged by this bookkeeping fix).

#### SUBSTEP 2.3 STATUS — superseded note (original destructive version)
`Reduction.hs`: replaced the 2.1 debug harness with `globalShapes :: [LPreskel]
-> [LPreskel]` (the homomorphism-maximal selection) and, at problem completion
(`breadth ... [] [] shapes`), emit each survivor via the stock
`commentPreskel lk [] [] Shape Nada ""` — i.e. proper `(defskeleton ... (shape))`.
Flag OFF: `shapes` is always empty there, so nothing is emitted and behavior is
stock.  `homDebugComment` removed.

The global-shapes path is now functionally complete.  `(shape)`-count check
(flag ON) vs stock:

| proto | stock | flag-ON | result |
|-------|-------|---------|--------|
| ns | 10 | 10 | MATCH |
| yahalom | 2 | 2 | MATCH |
| nsl3 | 3 | 3 | MATCH |
| envelope | 10 | 10 | MATCH |
| blanchet | 8 | 8 | MATCH |
| woolam | 12 | 12 | MATCH |
| dhstatic-state | 2 | 2 | MATCH |

- Survivors emit as complete shape defskeletons (full fields, label/parent,
  `(realized)`, `(shape)`); no debug artifacts remain.
- Flag OFF rebuilt: output **identical** to the 2.2 flag-off baseline (10 inline
  shapes, full 33-defskeleton stock tree).  "Flag OFF = stock" invariant intact.
- Known limitation (by design): with the flag ON the derivation tree no longer
  contains the realized leaves themselves (only survivors appear, at the end).
  Fine for shape counting / `cpsa4diff`; full per-leaf tree traceability is lost.
  Revisit only if Stage 3 needs it.

### Substep 2.4 — validation

#### New permanent tool: `cpsa4cmp` (shape-set isomorphism comparator)
`cpsa4diff` is useless here (it compares two runs S-expression by S-expression
and stops at the first textual difference; the flag-ON tree deliberately differs
from stock).  So we added `cpsa4cmp` (`src/CPSA/Cmp/Main.hs`, cabal stanza
`Executable cpsa4cmp`) — **kept as a permanent, generally-useful tool**.  It loads
the shape skeletons (every `defskeleton` carrying a `(shape)` marker, plus the
`defprotocol`s) from each output file via the standard `Loader`, then checks the
two collections are equal as multisets under skeleton isomorphism
(`isomorphic` on `gist`s — the exact equivalence CPSA uses internally).  It also
reports directional containment ("k/n of first matched in second") which pinpoints
over- vs under-reporting.  Usage: `cpsa4cmp FILE1 FILE2`; exit 0 iff iso-equal.

#### Suite-wide result (flag-OFF vs flag-ON, 127 tst/*.scm, 60s timeout each)
**123 / 127 ISOMORPHIC**, 0 skips/timeouts, **4 mismatches**:

| protocol | stock | flagON | containment | diagnosis |
|----------|-------|--------|-------------|-----------|
| nonaug-prune | 3 | 6 | stock ⊂ flagON (3/3; +3) | flag-ON keeps 3 more-specific leaves stock removes by **non-listener strand pruning** |
| ns-rebinding | 7 | 8 | stock ⊂ flagON (7/7; +1) | same pattern, +1 (protocol also exercises a rebinding `defrule`) |
| wonthull2 | 6 | 6 | 4/6 **both ways** | 2 shapes differ each way; the protocol's own header says it "demonstrates a subtle incompleteness" via "non-trivial deorigination" |
| dh-ca_hack | 70 | 69 | flagON ⊂ stock (69/69; −1) | flag-ON **drops one real (6-strand) shape** — the only under-report; DH |

So for the cases that match (the overwhelming majority, including the stateful
`dhstatic-state` and `envelope`), flag-ON shapes are **genuinely isomorphic** to
stock — answering the Stage-3 question (iso, not merely equinumerous, and not
merely homomorphism-related).

#### Interpretation of the 4 mismatches (for discussion, not yet acted on)
- **Over-reports (nonaug-prune, ns-rebinding): stock ⊂ flagON.**  Directly probes
  the core hypothesis.  These shapes are reached by stock via **non-listener
  strand deletion** (deleting strands made redundant *after* an augmentation).
  Forward search + listener-deletion does not produce the pruned (more-general)
  skeleton as an independent realized leaf, so global subsumption has no
  more-general leaf to subsume the un-pruned ones — they survive as extra shapes.
  Open question: is the pruned form actually a homomorphic image of the un-pruned
  leaf (then this is an `homomorphismExists` **false negative** to fix), or is the
  pruning "non-trivial" in a way that is not a pov-respecting strand-injective
  homomorphism (then it is a genuine limitation of the "listener-deletion-only"
  premise)?  nonaug-prune's name ("prune two strands ... after augmenting") and
  the clean `stock ⊂ flagON` containment point toward the latter.
- **wonthull2: divergence both ways.**  The protocol is explicitly a known
  incompleteness example involving deorigination; flag-ON and stock each find 2
  shapes the other does not.  Needs its own study.
- **dh-ca_hack: under-report (−1).**  [RESOLVED 2026-06-07 -- see "dh-ca_hack
  RESOLVED" below: this was NOT an under-report.  Stock OVER-reports (70);
  cpsa4subsume collapses the stock output to 69 too, isomorphic to the new
  path.  The extra stock shape survives only because variable separation hits
  its 1024 cap.  The new path's 69 is correct.]  Original (superseded) reading:
  The concerning direction: a real shape is
  missing.  Either (a) an `homomorphismExists` **false positive** wrongly subsumed
  a 6-strand leaf (possible DH-algebra gap in `skelToConj` and/or `validateEnv`),
  or (b) a reachability gap.  Since all 69 flag-ON shapes are valid stock shapes
  (69/69 matched), nothing spurious was produced — exactly one was lost.  Highest
  priority to diagnose.

Reproduce: stage two binaries (flag-off, flag-on), run each protocol with both,
then `cpsa4cmp off.txt on.txt`.

### Scope / risks
- **Unsupported with the flag ON (documented, guarded):** `--no-isochk` (`fast`),
  `optGoalsSat`, `optDepth` — their alternate `Shape` emit sites are not wired to
  the accumulator.  Either error out early when the flag and these options
  combine, or leave them on the stock inline path; decide at implementation.
- **Per-problem reset:** `shapes` is created in `mode` and consumed at
  `breadth ... [] []`, so it is naturally per-problem; leaves from different
  problems/povs are never compared (and `povSeed` rejects mismatched `prob`).
- **`homomorphism` is unexercised code:** mitigated by the oracle-agreement unit
  check and by keeping it as a validator behind the conjoin search.

### Stage 3 validation note
Because flag-ON over-reports, subsumption (removal-only) is the right tool. After
Stage 2, compare flag-ON shapes to stock. `cpsa4diff` (isomorphism-based) should
suffice IF the true shapes appear isomorphically among the leaves and the extras
are strictly more specific. If instead the surviving flag-ON shapes are strictly
more-specific specializations of stock shapes (homomorphism-related, not iso),
a homomorphism-based equivalence is needed. Determine which at Stage 3 (start
with yahalom: stock 2 vs flag-ON 8).

================================================================================
# 2026-06-07 — Approach A validated, pov-iso/collapse fixes, runtime flags,
#              deorigination, and in-search subsumption (Phases 4.1–4.2)
================================================================================

This section supersedes earlier speculation where they conflict.  It records
the path from the post-processor (Approach A) through the in-driver Option C.

## Tooling: cpsa4cmp and cpsa4subsume
- **cpsa4subsume** (post-processor): reads a listener-deletion-only run, splits
  it into problems at each `defprotocol`, loads the shape defskeletons, recovers
  each shape's `prob` from its `(maps …)` field, and rewrites every SUBSUMED
  shape's `(shape)` to `(seen S)(seen-ops (S (subsumption m)))`.  Direction:
  `homomorphismMapWith pj pi kj ki = Just m` means edge `j -> i` (j subsumes i,
  nstrands j <= nstrands i); the subsumed `i` records subsumer `j`.  Maximal
  shapes (subsumed by nobody) keep `(shape)`.
- **cpsa4cmp** (validator) — REWRITTEN this session: compares two shape files
  PER PROBLEM (same defprotocol split), matching shapes one-to-one under
  pov-respecting isomorphism (`probIsomorphicWith`), and reporting the witness
  pairing (`iso: Li <-> Lj`) plus `only in first/second` leftovers.  Fails loud
  on differing problem counts or per-pair protocol-name mismatch.  Removed the
  old global-zip and the `length pa==length pb` crash guard (within a problem all
  shapes share one pov, so prob lengths are equal by construction).

## Two stock bugs found and fixed (kept)
- **pov-respecting isomorphism** (user fix, verified): every live `isomorphic`
  became `probIsomorphic` and the one live `tryPerm` became `tryPermProb`.  The
  one remaining `isomorphic` in Reduction.hs `solve` compares the input to its
  skeleton form before any `prob` exists — intentionally left as `isomorphic`.
  This resolved nonaug-prune (stock was over-merging via a non-pov-respecting
  strand swap [1,0,2] that does not respect prob).
- **collapse fact-redundancy** (ns-rebinding): `collapseStrands` now resets to
  core facts (`withCoreFacts`) after collapse so rule re-application rederives
  cleanly, removing redundant existential facts.

## Phase 4.1 — runtime flags (DONE, validated byte-for-byte)
Converted the two compile-time constants to runtime `Options`, both defaulting
to the NEW path; two independent CLI flags turn each off:
- `Options.optGlobalShapes` (default True) — `--generalize` sets it False
  (restores full generalization).
- `Options.optDeorig` (default True) — `--no-deorig` sets it False.
Threading:
- `mkMode` (Reduction.hs) copies them into new `Mode` fields `globalShapes`,
  `deorig`.
- `deorig` flows `testNode/findTest -> solveNode/chanSolveNode -> augmentations
  -> roleAugs -> transformingNode` (Cohort.hs), gating the deorigination block.
- `globalShapes` flows `reduceNoTest -> maximize -> generalize/deleteNodes`
  (Strand.hs take a `Bool`; cannot take `Mode` — Strand is imported by Cohort).
- Deleted the `useDeorigination` constant (Cohort) and the `useGlobalShapes`
  constant + export (Strand); no external importers.
VALIDATION (= plan step 5): `cpsa4 --generalize --no-deorig` over all 127 .scm
is **byte-for-byte identical to Golden A** (127/127).  The runtime conversion
changed nothing on the stock path.

## Deorigination (wonthull2 completeness fix)
The augmentation `transformingNode` missed shapes where a transforming strand
must RECEIVE the critical term (sent via a send-only variable) rather than
ORIGINATE it.  `deoriginate` (gated by `deorig`): when the critical term is not
received anywhere in the past, also offer alternatives that bind a received
subterm to it and `fold` it within the escape set — KEEPING the originating
candidate too (both flow on; subsumption removes the non-maximal ones).
Earlier replace-not-keep and `mgs`-will-prune attempts failed; the correct
disposition is keep-both + GLOBAL subsumption (mgs cannot prune them — a strand
that receives a value is strictly more general than one that originates it).

### Deorig findings (Golden A vs Golden B, generalization path)
- Golden A = generalization, deorig OFF (= corrected stock), 127/127 clean.
- Golden B = generalization, deorig ON: 125/127 (timestamping TIMEOUT,
  wonthull2 ABORT).
- 122/127 ISOMORPHIC (deorig shape-neutral).  **Completeness GAINS** on:
  `incompleteness_example` (0->1), `deorig_simple` (0->1), `wonthull` (1->2),
  `wonthull3` (1->2) — each finds a legitimate decrypt/receive-and-retransmit
  shape stock misses (e.g. pov `send(enc n k) recv n`, gain `recv(enc n k)
  send n`).  `incompleteness_example` returning 0 under stock is a SOUNDNESS-
  relevant gap.  So deorig is "the right thing" well beyond wonthull2.
- COST: deorig on the *generalization* path is pathological (timestamping
  timeout, wonthull2 aborts) — its over-general candidates blow up mgs/thinning.
  Deorig belongs on the global+subsumption path; keep it OFF on the
  generalization path (also preserves Golden A as byte-for-byte stock).

## New-path reference (global + deorig + subsume) vs Golden A
`/tmp/golden_A` (deorig off), `/tmp/golden_B` (deorig on), `/tmp/newpath`
(global+deorig, with `.raw.txt` = pre-subsume candidates kept, `.txt` =
subsumed).  cpsa4cmp newpath-subsumed vs Golden A: **119 ISOMORPHIC**, 4 deorig
gains (each == Golden B, confirmed), 2 known variable-separation improvements
(ns-rebinding 7->8, dh-ca_hack 70->69), 2 perf failures.  Correct everywhere it
completes; only blocked by performance on 2 protocols.

### TWO DISTINCT performance problems (do not conflate)
1. **Subsumption O(n^2)** (wonthull2): cpsa4 emits 674 candidates fine; the
   post-processor `cpsa4subsume` times out (300s) on all-pairs.  FIXED by the
   in-search antichain (Phase 4.2).
2. **Generation explosion** (timestamping; wonthull2 @ bound 9): deorig
   over-generates so cpsa4 ITSELF times out / aborts before subsumption.  NOT
   fixed by 4.2.  Needs deorig generation-gating (Phase 4.4, DEFERRED): only
   deoriginate when the critical term already originates elsewhere in the
   skeleton (an illegal 2nd origination).

## Phase 4.2 — in-search homomorphism subsumption (Option C, DONE for verdicts)
Decisions: default = new path; two independent flags; Phase 4.3 output =
file-rewrite for `-o` + keep cpsa4subsume for pipes; Phase 4.4 deferred.
Implementation (Reduction.hs), accumulator carried as an IORef (user choice):
- `type ShapeCand = (Int, Preskel, [Sid])` (label, skeleton, prob).
- `IORef [ShapeCand]` created per problem in `solve`, threaded through
  `begin/search/mode/breadth/step/fast` (unchanged pass-through except two IO
  touch-points; `fast`/abort clauses bind `_sref`).
- Accumulate at the single `ReductStable` site, GLOBAL path only; still emit
  `(shape)` on both paths (comment marks where to switch the global-path marker
  to `(shape candidate)` once graph tooling is updated).
- End-of-problem (`breadth … [] []`): two passes.
  - `maximalShapes` (pass 1): fold candidates into an antichain.  drop-if-
    subsumed (incumbent subsumes newcomer -> drop newcomer); else evict-if-
    subsumes (newcomer subsumes incumbents -> remove them) and keep newcomer.
    No ties (search already removed pov-isomorphic dups), so order-independent.
  - `shapeVerdicts` (pass 2): for each non-maximal candidate, find a MAXIMAL
    shape that subsumes it (direct hom) and record `(subsumed, subsumer, map)`.
    The two-pass design guarantees every subsumed shape points at a SURVIVING
    shape with a DIRECT strand map — no subsumed->subsumed chains — matching
    cpsa4subsume's "prefer a maximal subsumer" and ready for the 4.3 rewrite.
  - `shapeSummary` emits `(comment "global-subsumption" (shapes …) (subsumed L
    by M (subsumption m)) …)`.  Cost ≈ 2n·|maximal| vs n^2.

### Phase 4.2 validation
- ns-rebinding: in-search maximal `[3,10,16,31,38,56,61,64]` IDENTICAL to
  cpsa4subsume survivors; 18 verdicts (26 candidates − 8).
- wonthull2 @ **bound 14** (herald bound 9 aborts under deorig): completes in
  10s, 699 candidates -> **6 maximal** (per-problem [2,4]), 693 verdicts — the
  result cpsa4subsume could not finish (300s timeout).  Demonstrates the
  subsumption perf cliff is gone.
- BROAD (all 127 at herald bounds): **MATCH=126, MISMATCH=0**, wonthull2 the
  only SUBSUME_TIMEOUT (= exactly the case in-search rescues).

### Phase 4.2 known gap
Aborted problems (strand/step limit) skip end-of-problem emission, so no summary
is produced for them (wonthull2 @ bound 9 emits only its first problem).  This
overlaps the deferred generation-explosion issue; revisit with Phase 4.4.

## Phase 4.3 — fold the rewrite in (full Option C, DONE for file output)
When output goes to a FILE (`-o`) on the global path, cpsa4 now applies the
in-search verdicts itself, producing a corrected file equivalent to a
cpsa4subsume run but without recomputing homomorphisms (so it inherits the
wonthull2 perf win).  stdout/pipes are unchanged: they keep the verdict
comments and rely on cpsa4subsume.
Implementation (Main.hs): after `solve` returns in `go`,
  `case (optGlobalShapes opts, optFile opts) of
     (True, Just path) -> applyGlobalSubsumption (optMargin opts) path; _ -> ...`
`applyGlobalSubsumption margin path`:
- reopens the finished file, reads all S-expressions strictly (`readAllSExprs`
  via `gentlyReadSExpr`, so it can reopen for writing),
- `collectVerdicts` parses `(comment "global-subsumption" … (subsumed L by M
  (subsumption m…)) …)` into `(L -> (M, m))`,
- `rewriteSubsumed` replaces each subsumed shape's `(shape)` with
  `(seen M)(seen-ops (M (subsumption m)))` (mirrors cpsa4subsume's orientation),
- drops the verdict comments (`isSubsumptionComment`), rewrites the file.
Helpers `isShapeForm`, `labelOf`, `strip` mirror cpsa4subsume.  Maximal shapes
keep `(shape)` (per the step-4 instruction; switch the global-path marker to
`(shape candidate)` once graph tooling is updated — TODO comment is at the
ReductStable accumulation site in Reduction.hs).

### Phase 4.3 validation
- ns-rebinding (`cpsa4 -o`): 8 maximal `(shape)`, 18 subsumption `(seen-ops)`,
  total `seen-ops` = 19 (matches cpsa4subsume; the +1 is a PRE-EXISTING stock
  duplicate-child `seen-ops`, unrelated to subsumption), verdict comments
  removed, and `cpsa4cmp` vs cpsa4subsume = ISOMORPHIC.
- Broad (cpsa4 -o vs Golden A, all 127, wonthull2 @ bound 14): SAME(iso)=120,
  DIFF=7, ERR=0.  The 7 DIFFs are exactly: 4 deorig gains (deorig_simple,
  incompleteness_example, wonthull, wonthull3) + 2 var-sep improvements
  (ns-rebinding +64, dh-ca_hack -159) + timestamping (generation timeout,
  deferred 4.4).  ERR=0 => every rewritten file parses cleanly.  120 = 119 +
  wonthull2: at bound 14 wonthull2 now completes and is ISOMORPHIC to Golden A
  (both 6), where the post-processor reference had it as an unparseable timeout.
  Outputs in /tmp/val43.

## Phase 4.3 follow-up — subsumption on ABORTED runs (bug found + fixed)
Testing the .lsp suite surfaced a bug: on an aborted run (strand/step limit)
the 4.3 file rewrite never ran, so all raw candidates survived un-subsumed
(dy.lsp: 266 shapes vs stock 2).  Root cause: `dump` ends the run by calling
`abort` (which exits the process), so control never returned to Main's
post-`solve` rewrite call.
Fixes (Reduction.hs):
- `emitShapeSummary` is now also called at the two abort points -- breadth's
  strand-bound clause and step's step-limit clause -- so the candidates found
  before the abort still get a subsumption pass (those clauses now use `sref`,
  formerly `_sref`).
- `applyGlobalSubsumption` was MOVED from Main.hs into Reduction.hs and wrapped
  as `finishGlobalShapes :: Options -> IO ()` (no-op unless global path + file
  output).  It is invoked at BOTH run-termination points: `solve []` (clean
  end) and `dump []` (abort end, before `abort`).  Main.go no longer calls it.
Result: dy.lsp -o now yields 2 shapes, ISOMORPHIC to corrected stock, even
though the run still aborts (exit 1 -- analysis incomplete but partial shapes
correctly subsumed).  General gain: any strand/step-limit abort on the new path
now emits a properly-subsumed shape set instead of raw candidates.

### .lsp suite validation (7 files)
new path vs corrected stock (`--generalize --no-deorig`): 7/7 ISOMORPHIC
(dy, epmo_acctnum, mass, mass2, neuman-stubblebine-reauth,
wide-mouth-frog-scyther, wide-mouth-frog).  Golden B (`--generalize`, deorig on)
== Golden A on all 7 (deorig shape-neutral here).  dy/mass/mass2/etc. abort on
the step limit on all paths (rc=1) but subsume correctly.

### Stock regression re-confirmed after 4.2/4.3/abort changes
`--generalize --no-deorig` over all 127 .scm: IDENTICAL=127, BYTEDIFF=0.  The
new-path machinery does not perturb the stock path.

## Full-suite 3-config comparison (both / gen / none)
Ran every .scm in three configs and compared pairwise with cpsa4cmp:
  both = --generalize --no-deorig (old cpsa)
  gen  = --generalize            (old + deorig)
  none = default                 (new subsumption path + deorig)
120/127 files: all three complete and ISOMORPHIC.  Only 7 non-trivial rows
(both/gen/none shape counts; differences as cfg:label):
- deorig completeness gains (gen==none, both misses one): deorig_simple (1/2/2),
  incompleteness_example (1/2/2), wonthull (2/3/3), wonthull3 (4/5/5).
- ns-rebinding (7/7/8): none keeps a shape BOTH generalization configs drop
  (variable separation loses it); subsumption MORE complete.
- dh-ca_hack (70/70/69): see resolution below.
- timestamping (2 / 0-timeout / 0-timeout): gen and none time out (deorig
  generation explosion, deferred Phase 4.4); only `both` completes.
No .scm aborted on a strand/step limit at its herald bound; the only incomplete
runs in the whole suite are timestamping's two deorig timeouts.  (wonthull2.scm
herald set to bound 14 so deorig completes.)  Table: /tmp/exp_all/table.md.

### dh-ca_hack RESOLVED (was logged above as a "concerning under-report")
Earlier notes flagged flag-ON's 69 vs stock 70 as possibly dropping a real
shape.  Resolved: it is the OPPOSITE -- generalization OVER-reports.  Running
cpsa4subsume on the generalization outputs collapses BOTH of them 70 -> 69, and
all three 69-sets (subsumed-both, subsumed-gen, new-path none) are mutually
ISOMORPHIC.  The extra stock shape (label 159 in this run) is homomorphically
subsumed by another shape; it survives stock only because variable separation
hits its 1024-subset cap and cannot merge it, whereas homomorphism subsumption
can.  So on dh-ca_hack the new path's 69 is the CORRECT (more general) answer,
not an under-report.  This is a second case (with ns-rebinding) where global
subsumption is strictly better than local generalization.

## Deorigination: cyclic-unification bug (timestamping) FIXED
The deorig generation explosion on timestamping (and any protocol with carried
mesg vars) turned out to be a genuine ALGEBRA bug, not a deorig-design flaw.

Root cause (found by bisection, full marker trace):
- The hang is a single non-terminating `Algebra.unify`.  `unify` ends with
  `chaseMap`, which fully resolves the substitution range via the RECURSIVE
  `substChase`.  The occurs-check in `unifyTerms` (`| occurs x t`) chases only
  SHALLOWLY, so it admits a TRANSITIVE cycle (x := f y while y := g x already in
  the subst).  `chaseMap` then loops forever resolving the cycle.
- Deorigination is the first thing that unifies a received message-sort variable
  with the critical term, which is exactly what can close such a transitive
  cycle.  Stock unification never creates one, so stock never hits it.
- Manifestation chain: the looping `unify` is inside `cmtUnify` in `deoriginate`;
  earlier it looked like the hang was in carriedOnlyWithin / augment, but those
  were never actually reached -- control never returned from `cmtUnify`.

Fix (Algebra.hs):
- New `acyclicSubst :: Subst -> Bool`: memoized three-colour DFS over the
  variable-dependency graph (key x -> the var Ids in the bound term).  Ids are
  collected by a plain recursive walk over every Term constructor (I/D/X vars +
  group var keys); do NOT use `foldVars`, which ERRORS on key-component forms
  like `(Invk (akey x))`/`(pubk x)` that occur in substitution ranges.
- `unify` now checks `acyclicSubst s` after `unifyChase` builds the substitution
  but BEFORE `chaseMap`; cyclic results fail cleanly (return []) instead of
  hanging.  This fires only on cyclic substitutions, which stock never produces,
  so flag-OFF stays byte-for-byte identical.
- `deoriginate` reverted to the clean cowt-based form (no mesg-var guard, no
  per-candidate acyclic guard); the unify-level fix handles it.

Validation:
- timestamping: 0s, 2 shapes, ISOMORPHIC to stock (was a >400s timeout).
- wonthull family + wonthull4 (mesg-var variant): 3 / 6 / 5 / 6, gains intact.
- STOCK byte-identity (`--generalize --no-deorig`, 127 .scm): IDENTICAL=126,
  FAIL=0 (the only diffs are wonthull2's intentional bound-14 herald and
  wonthull4 which has no golden ref).  Earlier this run FAILED=7 because the
  first `acyclicSubst` used `foldVars` and crashed; the recursive Id walk fixed
  it.  Wall time unchanged (~61s) -- the per-unify acyclic check is not a
  measurable slowdown.
- NEW path vs Golden A (full .scm suite): SAME(iso)=121, DIFF=6, ERR=0.  The 6
  are exactly the 4 deorig gains + ns-rebinding/dh-ca_hack var-sep.  timestamping
  is now in the 121 ISOMORPHIC.  This effectively resolves the deferred Phase 4.4
  generation-explosion concern -- timestamping was its motivating case.
- Test suite additions: tst/wonthull2.scm herald set to bound 14 (so the deorig
  search completes); tst/wonthull4.scm (user-added mesg-var deorig case).

## Current build/flag state
Default binary = NEW path (`optGlobalShapes=True`, `optDeorig=True`).  Stock via
`--generalize --no-deorig`; Golden B config via `--generalize`.  No rebuild
needed to switch (runtime flags).

## (shape candidate) marker (DONE)
On the global path a realized leaf is now emitted as `(shape candidate)` rather
than `(shape)`; the generalization path still emits `(shape)` (byte-identical to
stock).  Implementation (Reduction.hs): new `Kind` ctor `Candidate` with
`addKindKey Candidate = addKeyValues "shape" [S () "candidate"]` and
`isFringe Candidate = True`; the stable-reduct emit (both the breadth/step site
and the fast site) branches on `optGlobalShapes`; the `satisfies` key fires for
`Candidate` too.  After subsumption the SURVIVING candidates are promoted back
to plain `(shape)` and subsumed ones become `(seen ...)`, in BOTH the in-process
4.3 rewrite (`rewriteSubsumed`, new `promote`) and `cpsa4subsume`
(`emit`/`promoteShape`).  So `(shape candidate)` is the transient pre-subsumption
marker; a finished `-o` file (or a cpsa4subsume pipe) is form-identical to a
generalization-path result.  All downstream tools recognise `(shape candidate)`
via the existing `isShapeForm` (matches `(shape : _)`).  Verified: stock
byte-identical; new-path vs Golden A unchanged (cpsa4cmp is marker-agnostic).

## NEXT
- Phase 4.4 (deferred): deorig generation-gating -- NOTE this is now largely
  MOOT: the cyclic-unification fix made timestamping/wonthull complete, so the
  generation explosion that motivated 4.4 is gone.  Revisit only if a new
  protocol shows runaway generation.
- Comprehensive regression (plan step 6): full suite .scm then .lsp.
- Helper scripts: /tmp/gen_golden.sh, /tmp/gen_newpath.sh, /tmp/cmp_golden.sh,
  /tmp/validate_41.sh, /tmp/validate_42.sh, /tmp/gen_val43.sh.  Subplan in
  STEP4.md.
