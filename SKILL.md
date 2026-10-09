---
name: lean-certify
description: Build a certified computation in Lean 4 with the Lean certify library — theory states what holds, an untrusted fast producer computes a certificate, a checker proved sound certifies it in the kernel. Use when asked to certify, decide or check a property by computation in Lean (countermodels, derivations, bisimulations, any `by decide` on a large instance), to package an existing checker and soundness theorem as a `Certify.Certifier`, or when a fuelled search, `WellFounded.fix` decider or `native_decide` is being considered for a kernel check.
---

# Lean certify: the procedure

The pattern: *the theory says what; an untrusted fast producer computes it; a
checker proved sound certifies each product in the kernel.* Textbook names:
a *certifying algorithm* with a *verified checker*, discharged by *proof by
reflection*; the per-run half is *translation validation*. The full design is
`docs/outline.md` in github.com/fairflow/lean-certify; this file is the
working checklist.

Library: `import LeanCertify` (core Lean only, no Mathlib). Namespaces:
`Certify` (interfaces), `Harness` (configuration), `Certify.Lint` (lints).

## Glossary

- **Soundness** (of a checker): `check s c = true → Holds s`. The one
  obligation every certifier carries.
- **Exhaustiveness** (of an enumerator): a table the checker walks lists
  *every* object the theory has. A hypothesis of soundness, needed only when
  `Holds` is universal (bisimulation, invariance).
- **Completeness** (of a producer): whenever `Holds s`, the producer finds a
  certificate. Optional; never needed for a verdict. Fuel and bounds may
  appear in its statement and nowhere else.
- **Refinement**: a proved equation that on a validated certificate a fast
  evaluator equals the specification evaluator.

## The six steps

Do them in order. Do not start a step before the previous one's output exists.

1. **Theory.** Name the objects and the property `Holds : Spec → Sort u`
   (a proposition, or a type of derivations). State finiteness and
   termination facts as theorems. A measure (space bound, derivation
   height) is stated here and nowhere later. **No fuel or budget in `Holds`.**
   Send `Holds`, `Spec`, `Cert` and the type of `sound` to Matthew before any
   proof (R10). He is the gate and may supply an alternative.
2. **Certificate.** `Cert` is literal data (naturals, lists, a small
   inductive), with a prose description of its format. Every existential in
   `Holds` becomes a listed witness; every universal becomes a finite table
   the checker walks, with an exhaustiveness hypothesis. Known shapes:
   witness, closure set, relation with answering moves, proof trace, finite
   model.
3. **Checker and soundness.** `check : Spec → Cert → Bool`, structurally
   recursive (no `termination_by`, no `partial`, no `implemented_by`), and
   `sound : ∀ s c, check s c = true → Holds s`. Package them:
   ```lean
   def K : Certify.Certifier Spec Cert Holds := { check := …, sound := … }
   #certify_structural K       -- R3, must pass
   #certify_statement K        -- R2, must pass
   ```
4. **Producer, then minimisation.** `produce : Spec → Nat → Verdict Cert RCert`,
   compiled, untrusted, free to be `partial`. The `Nat` is a budget handed in
   at call time as a cheap over-approximation, **never computed from a
   materialised domain** (R1: run `#certify_domain produce`). An exhausted
   budget returns `.flag`, never `.fail`. Minimise the certificate (R6) as a
   separate untrusted stage; the checker is the only judge of the result.
5. **Splice.** Either a generated fact file (one line per fact,
   `theorem fact_i : Holds s_i := K.verdict s_i c_i`, a `def` when `Holds`
   is a type; commit the generating script beside it), or a tactic that runs
   the producer at elaboration time and leaves the certificate in the term.
   Above the project's chunk size, split one long `List.all` into chunks.
6. **Kernel check.** `K.verdict s c` reduces `K.check s c = true` with
   `by decide +kernel` (the default argument). Then:
   ```lean
   #certify_axioms fact_i      -- R4: within Harness.config.axioms
   ```
   and the **negative test** (R9): corrupt one certificate and watch the gate
   reject it, pinned with `#guard_msgs`. A gate never watched failing does not
   count. Record kernel time against certificate size (R8).

An engine bundles both sides: `Certify.Engine Spec Cert RCert Holds` with
`yes`, `no` (a certifier for `Holds s → False`; use `Certifier.empty` with
`RCert := Empty` when there is no refutation side) and `produce`.
`Engine.Complete` is optional and is the only place a budget may appear.

## The rules

- **R1. Never materialise the domain of a measure at run time.** Counting a
  formula space to compute fuel built the space (6 s on one sequent against
  34–72 ms at a hand fuel). `#certify_domain f` reports `Finset.card`,
  `Finset.powerset`, `Finset.product`, `Fintype.card`, `Finset.univ` on `f`'s
  evaluation path within the project. Reporting only.
- **R2. A fuelled engine explores failing branches to the fuel depth.** Use
  a fuel-free producer and check only its output. The `Certifier` type has
  no room for a budget; `#certify_statement K` rejects a `Holds` that
  mentions one (a constant or binder named with `fuel`/`budget`, or listed in
  `Harness.config.budgetNames`).
- **R3. Checkers are structurally recursive.** `WellFounded.fix` does not
  reduce in the kernel and is costly to elaborate. `#certify_structural f`
  rejects `WellFounded.fix`, `WellFounded.Nat.fix`, `._unary`/`._binary`
  auxiliaries, opaque constants (`partial def`) and `@[implemented_by]` on
  `f`'s evaluation path, core included.
- **R4. Axiom allow-list** `[propext, Quot.sound]` on every certified
  declaration; named exceptions in `Harness.config.axiomExceptions`; no
  per-certifier override. `native_decide` is excluded (its axioms fall
  outside the list). Mathlib's `Finset` brings in `Classical.choice`.
  Core `String` leaks it too, through the UTF-8 decoding proofs: `toList`,
  `length`, `trimAscii`, `contains`, `toLower` and `splitOn` reach
  `Classical.choice`. Clean: `==`, `decide (s = t)`, `isEmpty`,
  `String.ofList`, `toByteArray`; `++` needs only `propext`. This is pinned
  per toolchain in `LeanCertifyTest/ChoiceLeaks.lean` (v4.31.0 and v4.33.0).
- **R5. Three-valued verdict.** `fail` only with a refutation certificate;
  `flag` is rerun at a raised budget (`flagReruns`, `budgetFactor`) and never
  dropped; every skip and cap reported.
- **R6. Minimise certificates before the kernel check.** Kernel cost grows
  with certificate size.
- **R7. Bounded execution.** Run the compiled producer under a deadline
  (`deadlineSec`), not `lake exe` in a loop; report every skip.
- **R8. Measure and threshold.** Record kernel time against certificate
  size. A kernel check slower than `kernelTimeFlagSec` means the certificate
  is missing information: add a witness.
- **R9. Negative test.** Corrupt one certificate per checker; watch the gate
  reject it.
- **R10. Statements first.** `Holds`, `Cert` and the type of `sound` go to
  Matthew before any proof.
- **R11. External re-check.** `lean4checker` on certified modules is a test a
  project may run (`lean4checker := true`); not in the gate.

## Configuration

One constant per project, listing only what it changes:
```lean
def Harness.config : Harness.Config := { chunkSize := some 8 }
```
Per certifier: `@[harness splice := .tactic, minimise := false]` (fields:
`splice`, `minimise`, `chunkSize`, `deadlineSec`, `silenceDomainLint`). The
axiom list cannot be overridden per certifier. JSON for other tools:
`toJson Harness.config`.

## Do not

- use `native_decide`, or `implemented_by` on a checking path;
- put fuel in `Holds` or in a soundness statement;
- call a budget running out a failure;
- claim a certificate checked unless the kernel checked it with axioms
  pinned. A statement carrying `sorry` is OPEN.
