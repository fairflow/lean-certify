# Lean certify

A harness for certified computation in Lean 4: the theory says what must be
computed; an untrusted implementation, built for speed and faithful to the
theory, computes it; a checker proved sound certifies each product in the
kernel. Termination arguments stay in the theory and are never recomputed at
run time.

Status: V1 released (v0.1.0, 2026-10-09; current v0.1.2); v0.2 decisions
recorded, not built. Core Lean only (no Mathlib); pinned at Lean v4.31.0, checked on
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
(lints open the parameters of a generic certifier).

Licence: Apache-2.0 (see `LICENSE`).
