# Step 4: in-search homomorphism subsumption (Option C) + runtime flags

## Decisions (settled)
- **Default = new path**: global-shapes + deorig ON by default.
- **Two independent CLI flags** to turn each off (e.g. `--generalize` disables
  global-shapes; a separate flag disables deorig).  The pathological combo
  (generalization + deorig) stays reachable for diagnostics.
- **Phase 4.3 output**: when writing to a file (`-o`), rewrite it at the end
  with corrected shape markers; for stdout/pipe, emit verdict comments and let
  `cpsa4subsume` finish the job.  `cpsa4subsume` is retained as a validator.
- **Phase 4.4 (deorig generation-gating) deferred** to a later perf phase.

## Validation context (already established)
- Golden A (`/tmp/golden_A`): generalization, deorig OFF = corrected stock. 127/127.
- Golden B (`/tmp/golden_B`): generalization, deorig ON. 125/127 (timestamping
  timeout, wonthull2 abort).
- New-path reference (`/tmp/newpath`): global + deorig + subsume. vs Golden A:
  119 ISOMORPHIC, 4 deorig gains (== Golden B), 2 var-sep improvements
  (ns-rebinding 7->8, dh-ca_hack 70->69), 2 perf failures.
- Two distinct perf problems: wonthull2 = subsumption O(n^2) (Option C fixes);
  timestamping = deorig GENERATION explosion (needs Phase 4.4 gating, deferred).

## Hook points (Reduction.hs)
- Shapes are `ReductStable` skeletons (from `branch`, when `reduce` => `Stable`).
- Emitted in `step`'s `ReductStable` case (~ln 332-341), after `recall … seen`
  (strong pov-iso dedup).  This is the single shape-print site.
- `seen :: Seen` is the per-problem dedup state, threaded through
  breadth/step, merged across the parallel `branch` fan-out, reset per problem.
- `Mode` (Cohort.hs, built by `mkMode`, ln ~402) already threads into `reduce`.
- Compile-time flags to retire: `useGlobalShapes` (Strand.hs:212, used in
  generalize/deleteNodes) and `useDeorigination` (Cohort.hs:135, in
  transformingNode).

## STATUS (2026-06-07)
- 4.1 DONE & validated: `--generalize --no-deorig` == Golden A byte-for-byte (127/127).
- 4.2 DONE & validated: in-search maximal == cpsa4subsume survivors; broad run
  MATCH=126/127, MISMATCH=0, wonthull2 the only SUBSUME_TIMEOUT (the case 4.2
  rescues; wonthull2 @ bound 14 -> 6 shapes in 10s vs subsume 300s timeout).
  Verdicts emitted as `(comment "global-subsumption" …)`; each subsumed shape
  points at a maximal subsumer + direct map.  Known gap: aborted problems emit
  no summary (overlaps deferred 4.4).
- 4.3 DONE for file output (`-o`): after solve, Main.applyGlobalSubsumption
  reads the emitted global-subsumption verdict comments, rewrites each subsumed
  shape's (shape) -> (seen S)(seen-ops (S (subsumption m))), drops the comments.
  stdout/pipes keep comments + cpsa4subsume.  Validated: ns -o == cpsa4subsume
  (ISOMORPHIC, seen-ops match); broad cpsa4 -o vs Golden A: SAME(iso)=120,
  DIFF=7 (4 deorig gains + ns-rebinding/dh-ca_hack var-sep + timestamping
  timeout), ERR=0 (all rewritten files parse).
  Follow-up: switch global-path marker to (shape candidate) when graph tooling
  updated (TODO at ReductStable site).
- 4.3 follow-up: subsumption now also runs on ABORTED runs.  dump/abort exits
  the process, so applyGlobalSubsumption was moved into Reduction
  (finishGlobalShapes) and is called at both solve[] (clean) and dump[] (abort);
  emitShapeSummary added to the two abort clauses.  Fixed dy.lsp (266 -> 2,
  ISOMORPHIC to stock).
- .lsp suite: 7/7 new path == corrected stock (ISOMORPHIC).
- Stock byte-identity re-confirmed after 4.2/4.3/abort: 127/127.
- 4.4 DEFERRED.  Then plan step 6 (full regression: .scm then .lsp).
- Full detail appended to NOTES-global-shapes.md (2026-06-07 section).

## Phases
### 4.1 Runtime flags (do first; verify against Golden A)
- Add `Options` fields + CLI parsing; defaults = new path.
- Add fields to `Mode`; set in `mkMode`; `transformingNode` reads Mode.
- Thread the global-shapes flag into generalize/deleteNodes (Strand.hs).
- VALIDATE: flag to generalization+deorig-off, re-run suite, cpsa4cmp vs
  Golden A must be 127/127 ISOMORPHIC (== plan step 5).

### 4.2 In-search shape antichain + subsumption verdicts
- Per-problem `ShapeSet` of maximal candidates `(label, Preskel, prob)`.
- In `ReductStable` case, after iso `recall`, run antichain update via
  `homomorphismMapWith` (in-process; prob is live): drop-if-subsumed,
  evict-if-subsumes, else add.  Record subsumption edges.
- Keep emitting `(shape)` on every candidate (don't break graph coloring) but
  BRANCH the shape-writing on the runtime flag + comment where `(shape candidate)`
  goes later.  Emit verdicts as end-of-problem comments.
- VALIDATE: cpsa4subsume over this output finds nothing left to subsume.

### 4.3 Fold rewrite in (full Option C)
- File output: rewrite at end with corrected markers.  Pipe: verdict comments
  + cpsa4subsume.

### 4.4 Deorig generation-gating (DEFERRED)
- Only deoriginate when the critical term already originates elsewhere in the
  skeleton (illegal second origination).  Targets timestamping generation blowup.
