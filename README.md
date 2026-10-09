# Lean certify

A harness for certified computation in Lean 4: the theory says what must be
computed; an untrusted implementation, built for speed and faithful to the
theory, computes it; a checker proved sound certifies each product in the
kernel. Termination arguments stay in the theory and are never recomputed at
run time.

Status: V1 built (2026-10-09); `docs/v1-report.md` awaits review before the
`v0.1.0` tag. Core Lean only (no Mathlib); pinned at Lean v4.31.0, checked on
v4.33.0. Build the library with `lake build`, and the tests with
`lake build LeanCertifyTest`. The procedure, as a Claude skill, is `SKILL.md`.

- `docs/outline.md`: the design, as reviewed and decided by Matthew Fairtlough
  (2026-10-09). The specification for V1.
- `docs/v1-statements.md`: the V1 statements, approved by Matthew (R10).
- `docs/v1-report.md`: what V1 built, measurements, deviations.
- `docs/survey.md`: the prior-art survey behind it (certifying algorithms,
  proof by reflection, translation validation, Rocq extraction, Lean
  precedents).

Used by: [locus](https://github.com/fairflow/locus) (private) and
[lax-logic-in-lean](https://github.com/fairflow/lax-logic-in-lean), pinned by tag.

Licence: Apache-2.0 (see `LICENSE`).
