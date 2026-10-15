# Lean certify

A harness for certified computation in Lean 4: the theory says what must be
computed; an untrusted implementation, built for speed and faithful to the
theory, computes it; a checker proved sound certifies each product in the
kernel. Termination arguments stay in the theory and are never recomputed at
run time.

Status: v0.3.0 released (2026-10-15): deciders (prover, disprover,
fallback pairs; a settings registry; a command-line driver;
`docs/v0.3-statements.md`, `docs/deciders.md`); no changed signature.  It
contains v0.2.1 (2026-10-14): v0.2.0 (V1 plus chunking and
streaming, `@[csimp]` fast paths, and decisions (b) and (c);
`docs/v0.2-report.md`) with R3 on theorems (`docs/v0.2.1-statements.md`). Core Lean only (no Mathlib); pinned at Lean v4.31.0, checked on
v4.33.0. Build the library with `lake build`, and the tests with
`lake build LeanCertifyTest`. The procedure, as a Claude skill, is `SKILL.md`.

- `docs/outline.md`: the design, as reviewed and decided by Matthew Fairtlough
  (2026-10-09). The specification for V1.
- `docs/v1-statements.md`: the V1 statements, approved by Matthew (R10).
- `docs/v1-report.md`: what V1 built, measurements, deviations.
- `docs/v0.2-decisions.md`: decided for v0.2 (R3 and `implemented_by`; the
  shape of `Refinement`), not yet built.
- `docs/v0.2.1-statements.md`: R3 on theorems (what a proof decides by
  evaluation), allowances, and the walk into `@[implemented_by]`; released
  in 0.2.1.
- `docs/v0.3-statements.md`: deciders (prover, disprover, fallback pairs),
  the settings file and its generated JSON, backward compatibility;
  released in 0.3.0.
- `docs/deciders.md`: choosing a decider's tools, for a reader who does not
  know Lean.
- `docs/survey.md`: the prior-art survey behind it (certifying algorithms,
  proof by reflection, translation validation, Rocq extraction, Lean
  precedents).

Used by: [locus](https://github.com/fairflow/locus) (private) and
[lax-logic-in-lean](https://github.com/fairflow/lax-logic-in-lean), pinned by tag.

## Versioning

- A **patch release** (0.1.x) never changes a signature of the library's
  interface: `Certifier`, `Verdict`, `Engine`, `Refinement`, `Config`,
  `CertifierConfig`, the `@[harness]` attribute. A **minor release** (0.x)
  may, and must ship a migration note.
- **Downstream check before every tag.** Before tagging, build every known
  use against the candidate commit, under the budget rule (a kernel check
  under about 4 GB and 30 s per process; stop and report above about 15
  minutes), and tag only if all pass. Locus is private, so this runs
  locally, not in public CI.

Known downstream modules (keep this list current):

| Project | Module | Build |
|---|---|---|
| lax-logic-in-lean | `CertifyAdoption` (FinCM countermodels) | `lake build CertifyAdoption` |
| lax-logic-in-lean | `CertifyAdoption.CheckDeriv`, `LJF.OCheckDeriv` (derivation trees; main 4de06e9) | `lake build CertifyAdoption LJF.OCheckDeriv` |
| lax-logic-in-lean | `CertifyAdoption.Regression` (regression test: R1, R3, R4 pinned on every certifier, engine and theorem decided through one; one certified run per checker; main 0828de8; its CI builds it with the two above on every change of the pin) | `lake build CertifyAdoption.Regression` |
| locus (private) | `Logic.Certify` (bisimulation certificates) | `lake build LogicCertify` |
| locus (private) | `Logic.Examples.LinkModel.NeoSweep` (R3 over the Neo proof files) | `lake build Logic.Examples.LinkModel.NeoSweep` |
| locus (private) | on-demand certificates: `ABPCert`, `ABPOneCert`, `ABPRunsCert`, `ABPTrackBuff` (streamed by `certify_chunks`, assembled by `certify_all`), `ABPOneRel`, `M1Prime.ToyFast`, all under `Logic.Examples` | one module at a time, the rows files first (about 20 s and under 4 GB each): `lake build Logic.Examples.<name>` |

Releases: v0.1.0 (V1), v0.1.1 (R3: panic functions are leaves), v0.1.2
(lints open the parameters of a generic certifier), v0.1.3 (R4 runs
automatically on every `Certifier` and `Engine` declaration), v0.2.0 (V2:
chunking and streaming, `@[csimp]` fast paths; decisions (b) and (c)),
v0.2.1 (R3 on theorems: no vacuous pass; allowances), v0.3.0 (deciders:
prover, disprover, fallback pairs; settings registry; command-line driver).

## Migrating from 0.1.x to 0.2.0

0.2.0 is a minor release: one interface signature changes.

1. **`Refinement`** (decision (c), `docs/v0.2-decisions.md`). `fastEval`
   now takes the specification, `fastEval : Spec → Cert → Q → Bool`, and
   there is a domain, `dom : Spec → Cert → Q → Bool`. `refine` takes both
   hypotheses: `valid s c = true → dom s c q = true → fastEval s c q =
   specEval s q`. For the old meaning, write `dom := fun _ _ _ => true`, and
   give `fastEval` a first argument `_`. (No known downstream module used
   `Refinement` in 0.1.x.)
2. **R3 and `@[implemented_by]`** (decision (b)). Under the default
   `route := .kernel`, an `@[implemented_by]` constant on a checker's path
   is now an information note ("R3 note: …"), no longer an error. Under any
   other route it is still an error. A `#guard_msgs` that pinned the old
   error must be re-pinned. In locus, `Logic/Certify.lean` pins R3 on
   `wbisimCertifier` (`Match.guard`'s error strings reach `Nat.repr`); it
   now reads "R3 passes" followed by the note.
3. **New, nothing to migrate**: `Certify.all_of_chunks` and the commands
   `certify_chunks` / `certify_all` (chunking and streaming), and
   `Refinement.guarded`, `guarded_eq` and `certify_fastpath` (`@[csimp]`
   fast paths). The new commands are keywords: an identifier spelled
   `certify_chunks`, `certify_all` or `certify_fastpath` no longer parses.

## Changes in 0.2.1

0.2.1 is a patch release: no interface signature changes, but R3 is
stricter (`docs/v0.2.1-statements.md`).

1. **R3 on a theorem** no longer passes vacuously. `#certify_structural t`
   walks what `t`'s proof decides by evaluation (`of_decide_eq_true` and its
   siblings applied to a reflexivity proof, as `decide` and `decide +kernel`
   leave them), and reports `WellFounded.fix`, `WellFounded.Nat.fix` and the
   rest as **errors**; a theorem that decides nothing is an error ("nothing
   to walk"). `#certify_domain t` walks the same, or gives the same error.
   A `#guard_msgs` that pinned "R3 passes" or "R1: nothing to report" on a
   theorem must be re-pinned.
2. **`@[implemented_by]` under the kernel route** is still a note, but the
   walk now enters it (the kernel reduces its value). A checker that
   reaches a well-founded loop only through such a constant now fails R3:
   core `Array.contains` and `Array.any` do, through `Array.anyM.loop`.
3. **New: allowances.** `#certify_structural f allow c "reason", …`
   downgrades to a warning what R3 forbids at or below each named `c`; an
   allowance not on the path, or with nothing forbidden below it, is an
   error. `allow` is not a reserved word.

Downstream check (against this branch, local override): lax-logic-in-lean
`CertifyAdoption`, `CertifyAdoption.CheckDeriv` and `LJF.OCheckDeriv`, and
the private downstream module in the table above, all build unchanged.

## Changes in 0.3.0

0.3.0 is a minor release that changes no interface signature
(`docs/v0.3-statements.md`). A file that compiles against 0.2.1 compiles
unchanged; nothing is recoded.

1. **New: deciders** (`LeanCertify/Decider.lean`). `Certify.Prover` and
   `Certify.Disprover` separate the two sides of an engine; `Certify.Decider`
   is a prover, a disprover and fallback pairs tried in order;
   `Decider.run` races or sequences each pair, raises the budget on a flag,
   and returns a `Decision` carrying the proposition from `sound`. A
   certificate its certifier rejects is reported as a tool defect and
   ignored. An existing `Engine` plugs in through `Prover.ofEngine` and
   `Disprover.ofEngine`.
2. **New: the settings file.** `Harness.Registry` names the tools once;
   `Harness.DeciderConfig` chooses them by name; `#certify_decider` checks
   every name when the file compiles; `Certify.Cli.main` is the executable
   (flags `--deadline=`, `--budget=`, `--mode=`, `--json`). The JSON is
   generated from the Lean file, never read. A guide for readers who do not
   know Lean: `docs/deciders.md`.
3. **One proviso.** The new short names (`Prover`, `Disprover`, `Decider`,
   `Decision`, `Mode`, `RunConfig`, `tryPair`, `Cli` in `Certify`;
   `DeciderConfig`, `Tool`, `Registry` in `Harness`) can make an identifier
   ambiguous in a file that opens `Certify` or `Harness` and gives one of
   its own declarations the same short name. No known downstream file does.

Downstream check against the candidate 173b60a (the tagged commit changes
only `README.md` and `docs/v0.3-statements.md`), each project at its
current main with the pin moved to 173b60a in a scratch worktree:
lax-logic-in-lean `CertifyAdoption`,
`CertifyAdoption.CheckDeriv`, `CertifyAdoption.Regression` and
`LJF.OCheckDeriv` (v4.31.0; 72 s, every pinned message unchanged); locus
`LogicCertify` (v4.33.0; 10 s), `NeoSweep` (34 s; R3 passes on its 140
theorems proved by evaluation) and the 25 on-demand certificate modules
(401 s in all, the largest process 26 s and 3.6 GB). All build unchanged.

Licence: Apache-2.0 (see `LICENSE`).
