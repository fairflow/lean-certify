# A generic harness for certified computation in Lean 4: outline for review

For Matthew Fairtlough, 2026-10-09. Drafted by Fable 5.1 at the overseer's
request; revised the same day after Matthew's review (his decisions are in
section 9). Outline only: nothing was built, no Lean file was written,
nothing was committed. Reference numbers [n] are those of the prior-art
survey (`reports/certified-computation-survey.md`); no reference is added
here. File paths are read-only citations of locus (`main`, 659b759) and
lax-logic-in-lean (`origin/main`, 3ab5f41).

Every Lean signature below is a proposal and is OPEN. The only PROVED items
named are those already in a repository with a sorry-free proof, cited where
they occur.

## 1. Scope and non-goals

In scope: a fixed procedure and a small Lean library for the pattern
"theory says what; an untrusted fast producer computes it; a checker proved
sound certifies each product in the kernel". The textbook names are
*certifying algorithm* with a *verified checker* [1], [2], discharged by
*proof by reflection* [5], [6]; the per-run half is *translation validation*
[10]. Lean has no *program extraction* [36]–[38], so the producer is written
by hand and never trusted. The harness is one shared repository (a Lake
dependency of both projects) plus a skill (a written procedure for Claude).

Out of scope for V1: verifying the producer; any route that puts the
compiler in the trusted base (`native_decide`, `implemented_by` on the
checking path); streaming certificates [34] beyond chunking one literal; a
second, independent checker for the certificate format (survey gap 2);
interpolants (the LaxLogic findings put them last). Queued for V2:
`@[csimp]` refinement equations (section 7).

## 2. Glossary

Two properties were both called "completeness" in the inputs. The harness
uses two words.

- **Exhaustiveness** (of an enumerator). A table the checker walks lists
  *every* object the theory has: in locus, the matcher's enumeration contains
  every library move of a listed state (`cocc_G1`, the G1 guard, PROVED).
  It is a *hypothesis of soundness*, needed only when `Holds` is a universal
  property (bisimulation, invariance), because a missing row could let a
  false certificate pass.
- **Completeness** (of a producer). Whenever `Holds s` holds, the producer
  finds a certificate for it. Optional; never needed for a verdict; the OPEN
  half in LaxLogic (`CompletenessFRJO`, `search_complete_h`). Fuel and
  bounds may appear in its statement and nowhere else.
- **Soundness** (of a checker). `check s c = true` implies `Holds s`. The
  one obligation every certifier carries.
- **Refinement.** A proved equation: on a validated certificate, a fast
  evaluator equals the specification evaluator (locus M1′; an Isabelle code
  equation [45]; Lean `@[csimp]` [28]).

## 3. The pipeline

Six steps (the survey's eleven, Q5, merged; its steps 2, 9, 10 and 11 are
rules in section 6). For each: what the user supplies, what the harness
supplies, what is trusted, and the prior-art source.

### Step 1. Theory

- User supplies: the library objects; the property `Holds : Spec → Sort u`
  over them (a proposition, or a type of derivations); the finiteness or
  termination facts, as theorems. Any measure (a space bound, a derivation
  height) is stated here and nowhere later.
- Harness supplies: the requirement that `Holds` is named and reviewed by
  Matthew before any proof (R10), and that no fuel or budget appears in it.
- Trusted: the definitions. Everything downstream is relative to them.
- Source: Bove and Capretta [39] (termination argument is a proof, not
  code); locus `docs/logic-checking-plan.md`.

### Step 2. Specification of the certificate

- User supplies: the certificate type `Cert` as literal data (natural-number
  indices, lists, a small inductive), with a prose description of its format
  separate from the Lean type. Design rule: every existential in `Holds`
  becomes a listed witness; every universal becomes a finite table the
  checker walks, with an exhaustiveness hypothesis on the table.
- Harness supplies: the design rule; a checklist against the four known
  shapes: witness, closure set, relation with answering moves, proof trace.
- Trusted: nothing yet.
- Source: McConnell et al. [1] (witness property); LRAT hints [14], [15];
  Heath and Miller [20] (certificates for reachability and bisimulation).

### Step 3. Checker and its soundness theorem

- User supplies: `check : Spec → Cert → Bool`, structurally recursive, with
  no well-founded recursion, no `partial`, and no `Eq.rec` on its evaluation
  path; and `sound : check s c = true → Holds s`.
- Harness supplies: the `Certifier` interface (section 5); the structural
  lint (R3); the axiom pin (R4).
- Trusted: `check` and `sound`, as checked by the kernel; the axiom
  allow-list `[propext, Quot.sound]`.
- Source: Alkassar et al. [2] ("witness implies property" is the theorem to
  prove); Lean reference on recursion [25]; the `decide` docstring [27].

### Step 4. Fast producer, then minimisation

- User supplies: `produce`, compiled, untrusted, free to be `partial`, free to
  use any internal budget so long as the budget is supplied at call time as a
  cheap over-approximation and never computed from a materialised domain
  (R1). It emits a certificate, or a refutation certificate, or a flag.
- Harness supplies: the three-valued verdict type; the bounded-execution
  driver (R7); certificate minimisation (R6) as a separate untrusted stage
  that runs after `produce` and before the splice, on the certificate alone;
  a generator that writes certificates as Lean source literals with the
  generating script committed beside the output.
- Trusted: nothing.
- Source: translation validation [10], [11]; Rocq extraction erases bounds
  [38]; lax-logic `PROGRESS.md` §10 and `HANDOFF.md` §2026-08-26e; locus
  `docs/logic-checking-plan.md`.

### Step 5. Splice

- User supplies: the choice of splice point: a term inside a proof (a tactic
  that runs the producer at elaboration time and leaves the certificate in the
  term, as `pll_g4c` does in lax-logic) or a generated file of facts (locus
  `Logic/Examples/ABPCert.lean`; lax-logic `Certified/RhoRefutations.lean`).
- Harness supplies: both splice shapes; for the file shape, chunking of one
  long `List.all` into fixed-size pieces (locus `all_of_chunks` in
  `ABPCert.lean` is the existing instance).
- Trusted: nothing new; the splice only arranges where the kernel check runs.
- Source: `norm_num` and `polyrith` for the tactic shape [30], [31];
  the SAT practice for the file shape [13]–[16].

### Step 6. Kernel check

- User supplies: nothing beyond the files.
- Harness supplies: `by decide +kernel` on `check s c = true`, the
  application of `sound`, the per-file axiom pin (`#axioms_within`, present
  in both projects), the negative test (R9), the timing record (R8).
  `lean4checker` (R11) is a test the project may run; it is not in the gate.
- Trusted: the Lean kernel; `propext` and `Quot.sound`.
- Source: Boutin [5]; Barendregt and Barendsen [6]; Lean reference,
  "Validating a Lean proof" [24]; Carneiro [35].

## 4. The parameters

The survey's eight axes and the LaxLogic findings' eight parameters overlap;
merged, they are the eleven below. "Default" is what the harness does when
the project says nothing. Where each one is set is in section 8.

| # | Parameter | Choices | Default | locus | LaxLogic |
|---|---|---|---|---|---|
| P1 | Certificate kind | witness; closure set; relation plus answering moves; proof trace (derivation tree or proof term); finite model | witness | relation plus answering paths (`WBisimCert`) | proof term (`G4cTm`), finite model (`FinCM`), queued derivation tree |
| P2 | Checker evaluation route | kernel reduction; compiled under an axiom; external verified binary | kernel | kernel | kernel (two `native_decide` cardinality lemmas held out by name) |
| P3 | Axiom allow-list | `[propext, Quot.sound]`; plus `Classical.choice`; plus compiler trust | `[propext, Quot.sound]` | same, with named `Classical.choice` exceptions | same; `native_decide` excluded |
| P4 | Checker recursion | structural; fuel as structural recursion on a literal; well-founded (not kernel-reducible); `partial` (opaque) | structural | structural | structural (`checkB`, `search`); well-founded only outside checkers (`OFuelPFam`) |
| P5 | Measure placement | theory and the completeness theorem only; in the statement; on the run-time path | theory and completeness only | theory only (the state space is never counted) | theory and completeness (`search_complete_h`); `decideFuel` is the recorded counter-example |
| P6 | Verdict | two-valued; three-valued (pass, fail with a refutation certificate, flag) | three-valued, refutation side optional (`RCert := Empty`) | two-valued today (no refutation certifier for bisimulation) | three-valued (`Reject/Cert.lean` is the refutation side) |
| P7 | Faithfulness of the fast implementation | proved equation (refinement theorem; `@[csimp]` in V2); trusted replacement (`implemented_by`); no claim, output checked | no claim, output checked; a refinement theorem where the certificate validates a structure a second computation uses | refinement (`certCheck cert = true` implies the graph evaluator equals the library evaluator) | no claim (producers are `partial`); no `implemented_by` or `csimp` anywhere |
| P8 | Exhaustiveness hypothesis | none (existential or safety property); required and proved (universal property) | none | required, PROVED (`cocc_G1`), a hypothesis of `certBisimSound` | none |
| P9 | Completeness of the producer | not stated; stated and OPEN; proved | not stated | not stated | stated, OPEN (`CompletenessFRJO`); proved for the fuelled G4c search |
| P10 | Splice point | term in a proof (tactic); generated fact file; both | fact file | fact file | both (`pll_g4c` tactic; `RhoRefutations`, RNDB) |
| P11 | Size regime | one literal, one `decide`; chunked; split files; streamed | chunked above a per-project size | chunked (8 rows per `decide`, ABP at 112 and 160 states; about 5 min and 9.5 GB) | one literal per cell (hundreds of small cells) |
| P12 | Certificate storage | committed with its generator; regenerated per build | per project; committed if unset | committed | committed |

P8 and P9 replace the single "completeness" row of the first draft
(glossary). The LaxLogic list's bounded execution and certificate
minimisation are rules (R6, R7), not axes.

## 5. Interfaces as statements for review

All OPEN. `Holds` is Sort-polymorphic (decision 5): a proposition for
locus, a type of derivations for LaxLogic. Each block is followed by what it
says in plain words.

```lean
universe u

/-- A certifier: a Boolean checker and its soundness theorem. -/
structure Certifier (Spec Cert : Type) (Holds : Spec → Sort u) where
  check : Spec → Cert → Bool
  sound : ∀ s c, check s c = true → Holds s
```

A `Certifier` bundles the checker with its one obligation: if the checker
says yes on a specification and a certificate, the property holds of the
specification. Nothing about fuel, budgets or the producer can appear here,
because the signature has no room for it (R2 enforced by typing).

What changes with the sort. When `Holds s` is a proposition (`u = 0`, locus:
`WBisim …`; LaxLogic countermodels: `Γ ⊬ C`), `sound` is an ordinary theorem
and nothing differs from the Prop-only draft. When `Holds s` is a type
(`u = 1`, LaxLogic: `LSeq.holds`, a derivation), `sound` is a `def` that
*builds* the derivation from the certificate, as `search_sound` in
`LJF/OSearch.lean` already does; still kernel-checked and axiom-pinned, and
the derivation it returns is usable data. Eliminating the hypothesis
`check s c = true` into data is allowed because Boolean equality is
decidable (`anyWitness`, line 371, does exactly this).

```lean
/-- The three-valued verdict of an untrusted producer. -/
inductive Verdict (Cert RCert : Type) where
  | pass (c : Cert)      -- a certificate for Holds s
  | fail (r : RCert)     -- a certificate against Holds s
  | flag                 -- budget exhausted; rerun at a raised budget
```

`fail` is allowed only with a refutation certificate (a countermodel, a
non-derivability object); a budget running out is `flag`, never `fail`; a
`flag` is rerun and never dropped. The refutation side is optional:
`RCert := Empty` makes `fail` impossible.

```lean
/-- An engine: a certifier for the property, an optional one against it, and
    an untrusted producer. -/
structure Engine (Spec Cert RCert : Type) (Holds : Spec → Sort u) where
  yes : Certifier Spec Cert Holds
  no  : Certifier Spec RCert (fun s => Holds s → False)
  produce : Spec → Nat → Verdict Cert RCert    -- Nat is the budget; untrusted
```

The budget is a plain natural number handed in at call time (as `find` takes
10 000 in lax-logic). `produce` has no proof obligation; compiled code may
implement it with `partial def`. `Holds s → False` is the negation for both
sorts (no derivation exists). With `RCert := Empty`, `no` is the trivial
certifier whose `sound` has nothing to prove.

```lean
/-- Optional: completeness of the producer. Fuel appears here and only here. -/
def Engine.Complete (E : Engine Spec Cert RCert Holds) : Prop :=
  ∀ s, Holds s → ∃ n c, E.produce s n = .pass c
```

The only place a bound may appear. Optional; LaxLogic carries it OPEN;
locus does not state it.

```lean
/-- Optional: a refinement. A validated certificate makes a fast evaluator
    agree with the specification evaluator. -/
structure Refinement (Spec Cert Q : Type) (specEval : Spec → Q → Bool) where
  valid    : Spec → Cert → Bool
  fastEval : Cert → Q → Bool
  refine   : ∀ s c q, valid s c = true → fastEval c q = specEval s q
```

Some certificates validate a data structure (a state graph) on which a
second, cheap computation runs; the theorem says that on a validated
certificate the cheap computation equals the specification's (locus M1′,
`certCheck cert = true` implies `checkG = checkC`). In V2 the same equation
could be registered with `@[csimp]` so that one definition serves as kernel
checker and compiled fast path.

```lean
/-- The kernel gate: the checker's verdict carried to the property. -/
def Certifier.verdict (K : Certifier Spec Cert Holds) (s : Spec) (c : Cert)
    (h : K.check s c = true := by decide +kernel) : Holds s :=
  K.sound s c h
```

A generated fact file contains, per fact, one line
`theorem fact_i : Holds s_i := K.verdict s_i c_i` (a `def` when `Holds` is a
type), with the Boolean reduced by the kernel. Chunking (P11) replaces the
single `decide` by several, joined by a lemma like `all_of_chunks`.

## 6. Rules and lints

Each rule says whether it can be automated and how. "Constant walk" means a
metaprogram that collects the constants reachable from a declaration's
definition, the traversal `collectAxioms` performs.

- **R1. Never materialise the domain of a measure at run time.** The
  `decideFuel` case: a 54-digit fuel was free, but counting the formula space
  built it (6 s on one provable sequent; 34–72 ms at a hand fuel). Lint,
  adopted as *reporting only* (decision 8), no prior art (survey Q4 gap 6):
  a constant walk over the evaluation path of any `Decidable` instance or
  `produce` that flags `Finset.card`, `Finset.powerset`, `Finset.product`,
  `List.length` of an enumeration, or any `Nat` argument to a search that is
  not a literal or a parameter. False positives are expected.
- **R2. A fuelled engine explores failing branches to the fuel depth; use a
  fuel-free producer and check only its output.** On record: the fuelled
  search "ground for minutes" on refutable goals where `G4cTm.find` took 0 ms;
  compiled `searchProves` at fuel 64 was killed after about a day. Enforced by
  the `Certifier` signature; the remaining lint rejects any theorem on the
  certified path whose type mentions a budget. Automatable.
- **R3. Checkers are structurally recursive.** `WellFounded.fix` does not
  reduce in the kernel [25] and is costly to elaborate (`OFuelPFam.lean`:
  3 s as `unsafe`, 510 s without the kernel, 1 463 s committed). Lint:
  constant walk from `check`, rejecting `WellFounded.fix`, any `*._unary`
  auxiliary, `partial`, `implemented_by`. Automatable today.
- **R4. Axiom allow-list.** `[propext, Quot.sound]` on every certified
  declaration, checked by `collectAxioms` (`#axioms_within` in both
  projects); named exceptions at `Classical.choice`; `native_decide` excluded
  under both axiom spellings (`Lean.ofReduceBool` and the per-proof
  `…native_decide.ax_…`; lax-logic `scripts/ledger.lean` checks both).
  Automated already. The core lemmas that leak `Classical.choice` (locus
  `docs/protocol.md`) belong in the harness's documentation.
- **R5. Three-valued verdict.** `fail` only with a refutation certificate;
  `flag` rerun at a raised budget and never dropped; every skip and cap
  reported. Driver-level; automatable.
- **R6. Certificate minimisation before the kernel check.** An untrusted
  stage between `produce` and the splice: it takes a certificate and returns
  a smaller one, and the checker is the only judge of the result. Kernel cost
  grows with certificate size (the FRJ tables: minimisation "is what makes
  the final `by decide` affordable"). No lint; the timing record (R8) shows
  when it is missing. Whether it runs is a per-certifier setting.
- **R7. Bounded execution.** Run the compiled binary under a deadline, not
  `lake exe` (8.2 s of Lake overhead per check in lax-logic's measurements);
  report every skip. Driver-level; automatable.
- **R8. Measure and threshold.** Record kernel time against certificate size;
  "if a kernel check takes more than a few minutes, the certificate is
  missing information; add a witness" (locus). No calibrated threshold exists
  (survey gap 3); the threshold is per project (decision 9).
- **R9. Negative test.** Corrupt one certificate per checker and watch the
  gate reject it (locus did this for all five checkers). Automatable as a
  test that flips one index.
- **R10. Statements first.** `Holds`, `Cert` and the type of `sound` are a
  proposal that goes to Matthew before any proof; he is the gate and may
  supply an alternative statement. Procedure, not lint.
- **R11. External re-check.** `lean4checker` on certified modules
  (survey gap 1; [24], [35]). A test a project may run; not a rule and not
  in the gate (decision 4).

## 7. Three worked instances

### 7a. locus: weak bisimulation certificates

- `Spec`: the two signatures, the two tagged rule sets, the two initial
  states, and the side conditions the kernel also decides (G1 on both rule
  sets, the exhaustiveness hypothesis; the initial states well-formed, closed).
- `Cert`: `WBisimCert` (`Logic/CertBisim.lean`): two tagged graphs with
  renumbering witnesses, a relation on state indices, an answering path per
  obligation.
- `check`: `wbisimCheck`. `Holds`: `WBisim` of the two initial agents, a
  proposition (`u = 0`).
- `sound`: `certWeakBisimSound` (`Logic/CertBisimProof.lean`), PROVED, at
  `[propext, Quot.sound]`; the ABP instance `abp_wbisim_buff` in
  `Logic/Examples/ABPCert.lean`, PROVED by chunked `decide +kernel`.
- Fit: exact. The G1 and well-formedness hypotheses are Prop fields of
  `Spec`, decided separately. The `Refinement` structure also applies, for
  M1′ (`certCheck`, `checkG`, `checkC` in `Logic/M1Prime.lean`). No
  refutation certifier: `RCert := Empty`.

### 7b. LaxLogic: finite countermodels

- `Spec`: a sequent `(Γ, C)`. `Cert`: a finite model `FinCM` with a world
  index (`LaxLogic/PLL/Semantics/CountermodelEmit.lean` line 44: worlds
  `0 … n-1`, relation pairs, fallible worlds, valuation, all lists of
  naturals; a bare structure to keep `Classical.choice` out).
- `check`: `checkB M w Γ C` (line 239); `forceB` is structural on the
  formula with world quantifiers as folds over `List.range n`.
- `sound`: `not_provable_of_check` (line 261), PROVED, at
  `[propext, Quot.sound]`. `Holds s` is `Γ ⊬ C`, a proposition.
- Fit: exact; it is the `no` side of an `Engine` whose `yes` side is the
  proof-term route (`G4cTm`, kernel type-checking of a printed term, which
  needs no `check` because the kernel's type checker is the checker). The
  emitter, battery and minimiser are `partial`, untrusted, as expected.

### 7c. LaxLogic: `checkDeriv` for LJF◯ (queued 2026-08-26, unbuilt)

- `Spec`: a sequent `LSeq`. `Cert`: a derivation-tree datatype, to be
  defined (the rule table exists in `succs`, `LJF/OSearch.lean` line 88).
- `check`: `checkDeriv : Tree → LSeq → Bool`, structural on the tree, one
  clause per instance shape of `succs`. `produce`: `partial def emitTree`,
  compiled, untrusted.
- `sound`: `provable_of_checkDeriv`, OPEN, to be built from `succs_sound`
  (line 205, which rebuilds a derivation from any enumerated instance's
  premise derivations). `Holds` is `LSeq.holds`, a type (`u = 1`), so
  `sound` is a `def` returning the derivation.
- Fit: exact under the Sort-polymorphic `Certifier`; no `Nonempty` wrapper
  is needed. Fuel vanishes from the statement; `search_complete_h` (line 527)
  stays as the completeness theorem for the old fuelled search and is not
  needed for any verdict. This is the recommended first new build. Its scope,
  from the record: LJF◯, meaning the two-sided engine's proof side (which
  still re-runs a fuelled search in the kernel) and LJF-specific work. Table
  promotion is already served by G4c proof terms (`tools/RCellsGen.lean`).

All three now fit one `Certifier`. The remaining differences are optional
layers: `Refinement` (7a only); a refutation side (7b has one, 7a none);
exhaustiveness (7a only).

## 8. Where each setting enters, and how it is supplied

### (a) Where

"Who sets" is one of: *harness* (a default in the library), *project*
(one setting for the whole project), *certifier* (per `Certifier` or
`Engine` declaration, overriding the project), or *code* (not a setting at
all: a structural choice made when the types are written).

| Setting | Takes effect at | Who sets | Form |
|---|---|---|---|
| P1 certificate kind | step 2 | code, per certifier | the type `Cert` |
| P2 evaluation route | step 6 | project (V1 fixes `kernel`) | config field |
| P3 axiom allow-list | step 6, R4 | harness default; project adds named exceptions | config field |
| P4 checker recursion | step 3, R3 | code, per certifier; lint checks it | none |
| P5 measure placement | steps 1 and 3, R1, R2 | code; lints check it | none |
| P6 verdict | step 4 | code, per engine (`RCert`) | the type `RCert` |
| P7 faithfulness | step 3 | code, per certifier (a `Refinement` or nothing) | none |
| P8 exhaustiveness | step 2 | code, per certifier (a Prop field of `Spec`) | none |
| P9 completeness | after step 6, optional | code, per engine | `Engine.Complete` |
| P10 splice point | step 5 | certifier | config field |
| P11 size regime, chunk size | step 5 | project, certifier override | config field |
| P12 storage | step 5 | project | config field |
| R1 domain lint (reporting) | steps 3 and 4 | harness; project may silence per declaration | config field |
| R2 statement lint | step 3 | harness | fixed |
| R3 structural lint | step 3 | harness | fixed |
| R4 axiom pin | step 6 | harness, with P3 | fixed |
| R5 flag reruns (how many raises, by what factor) | step 4 | project | config field |
| R6 minimisation | between steps 4 and 5, untrusted | certifier (on or off, which minimiser) | config field |
| R7 deadline | step 4 | project, certifier override | config field |
| R8 kernel-time threshold | step 6 | project | config field |
| R9 negative test | step 6 | harness | fixed |
| R10 statements first | step 1 | Matthew | procedure |
| R11 `lean4checker` | after step 6, optional test | project | config field |

Only the rows marked "config field" are supplied as data; everything marked
"code" is a choice visible in the Lean declarations themselves, and the lints
read those declarations.

### (b) How: the supply format

Decided (Matthew, 2026-10-09): a per-project Lean file holding a typed
configuration structure, read by the lints and the gate directly. Typed (a
`Name` is a name, checked at elaboration); per-certifier overrides are an
attribute on the declaration; one source of truth; the config is ordinary
Lean data that never enters a proof, so it is untrusted and may be evaluated
by compiled code. Lakefile options were rejected (one flat set per package,
no per-certifier override). JSON or TOML is not a source: if a non-Lean tool
ever needs the values, they are generated from the Lean file (`ToJson`).

Sketch of the structure, OPEN:

```lean
namespace Harness

inductive Route | kernel | native | external
inductive Splice | factFile | tactic
inductive Storage | committed | regenerated

/-- Project-wide settings, one constant per project. -/
structure Config where
  route           : Route := .kernel                       -- P2
  axioms          : List Name := [``propext, ``Quot.sound] -- P3, R4
  axiomExceptions : List (Name × List Name) := []          -- named declarations
  chunkSize       : Option Nat := none                     -- P11
  storage         : Storage := .committed                  -- P12
  flagReruns      : Nat := 2                               -- R5: raises of the budget
  budgetFactor    : Nat := 4                               -- R5: multiplier per raise
  deadlineSec     : Nat := 600                             -- R7
  kernelTimeFlagSec : Nat := 180                           -- R8
  lintDomain      : Bool := true                           -- R1, reporting
  lean4checker    : Bool := false                          -- R11, a test
  deriving Repr, ToJson

/-- Per-certifier overrides, attached by attribute to a `Certifier` or
    `Engine` declaration: `@[harness splice := .tactic, minimise := false]`. -/
structure CertifierConfig where
  splice      : Splice := .factFile                        -- P10
  minimise    : Bool := true                               -- R6
  chunkSize   : Option Nat := none                         -- P11 override
  deadlineSec : Option Nat := none                         -- R7 override
  silenceDomainLint : Bool := false                        -- R1 per declaration
  deriving Repr, ToJson

end Harness
```

The project supplies `def Harness.config : Harness.Config := { … }` in one
file (say `Harness/Config.lean` in the project), listing only the fields it
changes. The lints look up `Harness.config` in the environment and evaluate
it; the attribute stores a `CertifierConfig` per declaration in an
environment extension. `#eval (toJson Harness.config)` writes the JSON the
deadline runner and the generator read. A field that must not be weakened
per certifier (the axiom list) deliberately has no override in
`CertifierConfig`.

## 9. Staging

V1, small, in one shared repository (name to be chosen, decision 14), a
Lake dependency of both projects:

1. `Certifier.lean`: `Certifier`, `Verdict`, `Engine`, `Engine.Complete`,
   `Refinement`, `Certifier.verdict` (section 5; about 60 lines).
2. `Config.lean`: the two configuration structures and the attribute
   (section 8).
3. `Lint.lean`: the structural lint (R3), the statement lint (R2), and the
   domain lint (R1, reporting); the axiom check reuses `#axioms_within`.
4. `SKILL.md`: the procedure of section 3 as a checklist, the rules of
   section 6, and the glossary.

Acceptance test, run in lax-logic (no new proof needed): package
`FinCM.checkB` and `not_provable_of_check` as a `Certifier` without changing
either; reproduce one refutation from `Certified/RhoRefutations.lean`
through `Certifier.verdict`; pin at `[propext, Quot.sound]`; corrupt the
model's valuation and watch the gate reject it (required: `checkB` is
sound but incomplete, since it only evaluates the model it is given, and a
gate never watched failing does not count); run the structural lint on
`checkB` (must pass) and on the Iemhoff G4 decider defined by
`WellFounded.fix` (`docs/g4ill-gap-review.md` line 55; must flag); run the
domain lint on `decideFuel` (must report); read the project's
`Harness.config` from the lint.

Second stage: `checkDeriv` (7c), the first new build, judged by the queued
criterion: campaign theorems become `laxND_of_checkDeriv (by decide)` on a
tree literal with kernel cost linear in tree size. Third stage: retrofit
locus's `WBisimCert` to the same `Certifier` and add the `Refinement`
instance for M1′, as a check that the shape holds across projects.

V2 (named here so it is not lost): `@[csimp]` refinement equations, so one
definition serves as kernel checker and compiled fast path (survey open
question 4); streaming beyond chunking if a certificate outgrows one file.

## 10. Decisions taken (Matthew, 2026-10-09)

1. One shared repository, used by both projects.
2. Both a skill and a Lean library.
3. `@[csimp]` refinement equations: queued for V2, out of V1.
4. `lean4checker`: a test only, not a rule and not in the gate.
5. `Holds` is Sort-polymorphic (section 5 rewritten; 7a–7c all fit).
6. Two names for the two properties (glossary, section 2).
7. The refutation side is optional; `RCert := Empty` is legal.
8. The R1 lint is adopted, reporting only.
9. Chunk size and kernel-time threshold are per project.
10. Committed versus regenerated certificates is per project.
11. R10 stands: the statements are a proposal and Matthew is the gate.
12. Settings are supplied in a per-project Lean file (`Harness.Config`,
    section 8b); JSON only ever generated from it.

13. The word for the enumerator property is *exhaustiveness*; *completeness*
    is kept for the producer.
14. The shared repository is called **Lean certify** (repository name
    `lean-certify`); projects pin it by tag.
15. Per-certifier overrides as sketched: splice, minimisation, chunk size and
    deadline may be overridden; the axiom list may not.
16. `Certifier.verdict` carries `by decide +kernel` as a default argument.

## Discrepancies found in the inputs (all resolved)

- Fuelled LJF◯ checking has two uses (LaxLogic manager, 2026-10-09). RCells
  table promotion was replaced by the G4c proof-term route
  (`tools/RCellsGen.lean`); `docs/next-session.md` 427–447 is stale. The
  two-sided engine's proof side (`wip/ljfo_link.lean`,
  `laxND_of_searchProves (f := 16) (by decide)`) still re-runs the search
  under fuel in the kernel; that is `checkDeriv`'s scope (7c).
- The per-proof native axioms are present under Lean 4.31; the survey's
  "4.35" was wrong for that repository and is corrected.
- Mathlib's `Finset` brings in `Classical.choice` (findings, cause 4) but
  `G4Dec.lean` audits clean through a choice-free `Finset` kit: the rule is
  "avoid Mathlib's `Finset` unless through the choice-free kit".
- "Completeness" in two senses: separated by the glossary (decision 6).

🕒 2026-10-09 15:32 BST
— Fable 5.1 · effort unknown
