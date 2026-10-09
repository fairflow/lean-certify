# Lean certify V1: report

For Matthew, 2026-10-09. Built to `docs/outline.md` §9 by Opus 5.5. The
statements of `Certifier.lean` and `Config.lean` were sent first
(`docs/v1-statements.md`) and approved (R10), together with the toolchain pin
and keeping `WellFounded.Nat.fix` rejected. Licence: Apache-2.0 (Matthew).
Status: everything below is built and pushed. The tag `v0.1.0` awaits your
approval of this report.

## What was built

lean-certify `main`, df1d016. Core Lean only, no Mathlib. `lean-toolchain` is
pinned at v4.31.0, and every commit was also built on v4.33.0.

| File | Lines | Contents |
|---|---|---|
| `LeanCertify/Certifier.lean` | 68 | `Certifier`, `Verdict`, `Engine`, `Engine.Complete`, `Refinement`, `Certifier.verdict` (default `by decide +kernel`), `Certifier.empty`; namespace `Certify` |
| `LeanCertify/Config.lean` | 125 | `Harness.Config`, `Harness.CertifierConfig`, the `@[harness …]` attribute (persistent extension), `Harness.readConfig` |
| `LeanCertify/Lint.lean` | 314 | `#certify_structural` (R3), `#certify_statement` (R2), `#certify_domain` (R1, reporting), `#certify_axioms` (R4) |
| `SKILL.md` | 135 | The six steps, rules R1–R11, glossary, configuration, as a Claude skill |
| `LeanCertifyTest/*.lean` | 277 | Each gate and lint watched passing and failing; 24 `#guard_msgs` pins |

## The lints, as built

All four are *constant walks*. A walk follows the values of the definitions
it reaches; it does not enter theorems, inductives, or opaque constants. Each
reported constant comes with the chain of definitions that reaches it.

- **R3 `#certify_structural f`** (error). For a `Certifier` or `Engine` it
  walks only the `check` functions; `sound` is a proof and `produce` is
  untrusted. It enters every module, core included. It rejects
  `WellFounded.fix`, `WellFounded.fixF`, `WellFounded.Nat.fix`,
  `._unary`/`._binary` auxiliaries, opaque constants (`partial def`), and
  `@[implemented_by]`. Leaves: the 14 `Nat` operations the kernel computes
  natively on literals (see deviation 3).
- **R2 `#certify_statement K`** (error). It walks from the `Holds` of `K`
  through the project's own definitions; library modules are not entered. A
  constant counts as a budget if its name or one of its binder names contains
  `fuel` or `budget`, or if it is listed in `Harness.config.budgetNames`.
  Binder names inside `Holds` itself are checked too.
- **R1 `#certify_domain f`** (warning only). It reports `Finset.card`,
  `Finset.powerset`, `Finset.product`, `Fintype.card` and `Finset.univ`
  within the project's modules. It respects `Harness.config.lintDomain` and
  `@[harness silenceDomainLint := true]`.
- **R4 `#certify_axioms f`** (error). It runs `collectAxioms` against
  `Harness.config.axioms` plus the exceptions that config names for `f`.

## The acceptance test

lax-logic-in-lean, branch `certify-adoption`, commit 4a05d4c (parent
`main` 824032e). It is one module, `CertifyAdoption.lean` (140 lines,
12 `#guard_msgs` pins), outside `defaultTargets`, with lean-certify pinned
at df1d016. `CountermodelEmit.lean` is unchanged. The lakefile and manifest
only gain the dependency and the library. Arranged with the LaxLogic manager,
who accepted the results.

| Requirement (§9) | Result |
|---|---|
| Package `FinCM.checkB` and `not_provable_of_check` as a `Certifier`, unchanged | `countermodel : Certifier (List PLLFormula × PLLFormula) (FinCM × Nat) (fun s => s.1 ⊬ s.2)`, `sound _ _ h := FinCM.not_provable_of_check h` |
| Reproduce one refutation of `RhoRefutations.lean` through `Certifier.verdict` | `rho_1_nle_4 : [ρ1] ⊬ ρ4`, the 3-world model `cm_rho_1_4` transcribed from its `Tab` |
| Pin at `[propext, Quot.sound]` | `#print axioms` and `#certify_axioms` both pinned |
| Corrupt the valuation; watch the gate reject | `checkB = false` proved by `decide +kernel`, and `verdict` fails to elaborate, for two models (deviation 1) |
| Structural lint on `checkB` must pass | Passes, on `FinCM.checkB` and on `countermodel` |
| Structural lint on the `WellFounded.fix` G4 decider must flag | `G4.decideG4` flagged: `WellFounded.fix` |
| Domain lint on `decideFuel` must report | Reports `Finset.card` [Mathlib.Data.Finset.Card] |
| Read the project's `Harness.config` from the lint | The test's config (`kernelTimeFlagSec := 60`) is read back |
| (added) R2 on the certifier | Passes |

## Measurements

| What | Wall | Peak RSS |
|---|---|---|
| `lake build CertifyAdoption`, first (clones lean-certify, checks 8 594 jobs) | 54.6 s | 5.65 GB |
| The same after a lean-certify bump (module 16 s) | 24.6 s | 5.80 GB |
| lean-certify library and tests, v4.31.0 or v4.33.0 | a few seconds per module | — |

In lax-logic no Mathlib module and no LaxLogic module was rebuilt; `.lake` was
an APFS clone of the `merge-main` worktree. Almost all of the memory is the
loading of Mathlib's `.olean`s; the kernel checks themselves are small (models
of 2 and 3 worlds). R8, kernel time against certificate size, is not
calibrated in V1.

## Deviations from the outline, and why

1. **The corrupted valuation.** The ρ formulas are closed (no atoms), so the
   only valuation `cm_rho_1_4` has is that of `⊥`, which is the fallible set.
   I corrupted that set, so that `ρ4` became forced at the root. To corrupt a
   valuation proper as well, the test adds `◯p ⊬ p` on two worlds, with `p`
   made true at the root. Both corruptions are rejected.
2. **R3 passes `decideFuel`.** `decideFuel` is closed-form arithmetic, so it is
   structural. Its fault is materialising `enum` to count it (R1), and R1
   reports it. The LaxLogic manager agrees, and the test records "R1 rejects,
   R3 passes, by design".
3. **The kernel's `Nat` operations are leaves of the R3 walk.** A sparse
   `match` compiles to a `_sparseCasesOn` auxiliary that calls `Nat.land`.
   `Nat.land` is defined through `Nat.bitwise._unary` (well-founded), so the
   first version of the lint rejected `decideG4` for this spurious reason as
   well as the real one. The exemption is exactly the set of binary cases in
   the kernel's `type_checker::reduce_nat` (`src/kernel/type_checker.cpp`,
   identical at v4.31.0 and v4.33.0): add, sub, mul, pow, gcd, mod, div,
   beq, ble, land, lor, xor, shiftLeft, shiftRight. `Nat.log2` is not among
   them, and the LaxLogic manager confirmed this independently. A test
   watches a user-defined function of `Nat.bitwise`'s shape still rejected.
4. **`WellFounded.Nat.fix` is rejected, though it reduces.** In this Lean,
   well-founded recursion on a `Nat` measure compiles to a fuelled `Nat.rec`
   that the kernel does reduce (`wfLog 8 = 3` by `decide +kernel`). It is
   rejected, as you decided.
5. **Small additions to the interface, approved.** The namespace `Certify`,
   `Certifier.empty`, `Verdict` deriving `Repr`, and
   `Config.budgetNames`.
6. **R2's notion of a budget is a heuristic**: names and binder names
   containing `fuel` or `budget`, plus `budgetNames`. A budget under any
   other name, in a library definition, is not caught.
7. **Not in V1.** R1 does not detect "`List.length` of an enumeration" or "a
   computed `Nat` argument to a search", because neither has a syntactic test
   I could make precise. Also missing: the chunking helper (`all_of_chunks`),
   the bounded-execution driver (R5, R7), the minimiser hook (R6), the
   timing record (R8), and the JSON writer beyond `toJson`. The config fields
   for these exist, but nothing reads them yet.
8. **R3 and `Name` literals.** The `Lean.Name` constructors carry
   `@[implemented_by]`, so a checker that builds `Name`s would be rejected.
   This was seen once, on an ill-typed test, and never on a real checker.
   Left as is.

## Next

- Tag `v0.1.0` on your approval; then the lax-logic require moves from the
  commit to the tag.
- Merging `certify-adoption` to lax-logic `main` is your decision.
- Second stage, as in outline §9: `checkDeriv` (7c). Third stage: retrofit
  locus's `WBisimCert`.
