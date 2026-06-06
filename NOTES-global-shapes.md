# Experiment: Global Shape Subsumption

Branch: `experiment/global-shape-subsumption` (CPSA 4.4.9).
Status: planning. Nothing implemented yet.

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
