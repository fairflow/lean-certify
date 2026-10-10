# Lean certify

A harness for certified computation in Lean 4: the theory says what must be
computed; an untrusted implementation, built for speed and faithful to the
theory, computes it; a checker proved sound certifies each product in the
kernel. Termination arguments stay in the theory and are never recomputed at
run time.

Status: v0.2.0 released (2026-10-10): V1 plus chunking and streaming,
`@[csimp]` fast paths, and decisions (b) and (c); `docs/v0.2-report.md`. Core Lean only (no Mathlib); pinned at Lean v4.31.0, checked on
v4.33.0. Build the library with `lake build`, and the tests with
`lake build LeanCertifyTest`. The procedure, as a Claude skill, is `SKILL.md`.

- `docs/outline.md`: the design, as reviewed and decided by Matthew Fairtlough
  (2026-10-09). The specification for V1.
- `docs/v1-statements.md`: the V1 statements, approved by Matthew (R10).
- `docs/v1-report.md`: what V1 built, measurements, deviations.
- `docs/v0.2-decisions.md`: decided for v0.2 (R3 and `implemented_by`; the
  shape of `Refinement`), not yet built.
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
| lax-logic-in-lean | `CertifyAdoption.CheckDeriv`, `LJF.OCheckDeriv` (derivation trees; main 4de06e9; its CI builds `LJF.OCheckDeriv` only) | `lake build CertifyAdoption LJF.OCheckDeriv` |
| locus (private) | `Logic.Certify` (bisimulation certificates) | `lake build LogicCertify` |

Releases: v0.1.0 (V1), v0.1.1 (R3: panic functions are leaves), v0.1.2
(lints open the parameters of a generic certifier), v0.1.3 (R4 runs
automatically on every `Certifier` and `Engine` declaration), v0.2.0 (V2:
chunking and streaming, `@[csimp]` fast paths; decisions (b) and (c)).

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

Licence: Apache-2.0 (see `LICENSE`).
