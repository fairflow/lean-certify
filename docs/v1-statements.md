# Lean certify V1: statements for review (R10)

**Approved by Matthew, 2026-10-09:** the statements as below; toolchain pinned
at v4.31.0; `WellFounded.Nat.fix` stays rejected by R3.

For Matthew, 2026-10-09. These are the signatures and definitions of
`LeanCertify/Certifier.lean` and `LeanCertify/Config.lean` as written. Both
type-check on Lean v4.31.0 and v4.33.0, core `Lean` only, no Mathlib. No proof
or lint that depends on them has been written; the structural lint (R3) and
the domain lint (R1) take an arbitrary constant, so I am building them
meanwhile. Everything below is OPEN until you approve it or supply an
alternative.

## Certifier.lean (namespace `Certify`)

```lean
universe u

structure Certifier (Spec Cert : Type) (Holds : Spec → Sort u) where
  check : Spec → Cert → Bool
  sound : ∀ s c, check s c = true → Holds s

inductive Verdict (Cert RCert : Type) where
  | pass (c : Cert) | fail (r : RCert) | flag

structure Engine (Spec Cert RCert : Type) (Holds : Spec → Sort u) where
  yes : Certifier Spec Cert Holds
  no : Certifier Spec RCert (fun s => Holds s → False)
  produce : Spec → Nat → Verdict Cert RCert

def Engine.Complete (E : Engine Spec Cert RCert Holds) : Prop :=
  ∀ s, Holds s → ∃ n c, E.produce s n = .pass c

structure Refinement (Spec Cert Q : Type) (specEval : Spec → Q → Bool) where
  valid : Spec → Cert → Bool
  fastEval : Cert → Q → Bool
  refine : ∀ s c q, valid s c = true → fastEval c q = specEval s q

def Certifier.verdict (K : Certifier Spec Cert Holds) (s : Spec) (c : Cert)
    (h : K.check s c = true := by decide +kernel) : Holds s :=
  K.sound s c h

def Certifier.empty : Certifier Spec Empty Holds where
  check _ c := nomatch c
  sound _ c := nomatch c
```

Differences from outline §5, all small:

1. **Namespace `Certify`.** The outline leaves `Certifier` and the rest at the
   root. A shared library should not claim root names; neither project
   defines any of these names today (checked), but I would rather not take
   them. The config stays in `Harness`, as sketched.
2. **`Certifier.empty`** is added: the trivial certifier with `Cert := Empty`,
   so that an engine without a refutation side (decision 7) writes
   `no := .empty`.
3. `Verdict` derives `Repr`, nothing else.

## Config.lean (namespace `Harness`)

```lean
inductive Route   | kernel | native | external
inductive Splice  | factFile | tactic
inductive Storage | committed | regenerated

structure Config where
  route             : Route := .kernel                       -- P2
  axioms            : List Name := [``propext, ``Quot.sound] -- P3, R4
  axiomExceptions   : List (Name × List Name) := []
  chunkSize         : Option Nat := none                     -- P11
  storage           : Storage := .committed                  -- P12
  flagReruns        : Nat := 2                               -- R5
  budgetFactor      : Nat := 4                               -- R5
  deadlineSec       : Nat := 600                             -- R7
  kernelTimeFlagSec : Nat := 180                             -- R8
  lintDomain        : Bool := true                           -- R1
  budgetNames       : List Name := []                        -- R2  (new)
  lean4checker      : Bool := false                          -- R11
  deriving Repr, ToJson, FromJson

structure CertifierConfig where
  splice            : Splice := .factFile                    -- P10
  minimise          : Bool := true                           -- R6
  chunkSize         : Option Nat := none                     -- P11
  deadlineSec       : Option Nat := none                     -- R7
  silenceDomainLint : Bool := false                          -- R1
  deriving Repr, ToJson, FromJson, Inhabited
```

The attribute: `@[harness splice := .tactic, minimise := false]` on a
declaration. Each field is elaborated against `CertifierConfig` and stored in a
persistent environment extension. A field that is not in `CertifierConfig` is
an error, so `@[harness axioms := []]` is rejected with "the axiom list has
no per-certifier override" (I watched this fail). The lints read the
project's `Harness.config` constant by evaluating it, and fall back to the
defaults if the project declares none. Tested: `toJson` of a project config
with `chunkSize := some 8` prints the expected JSON.

Difference from the outline §8b sketch:

4. **`budgetNames : List Name`** is new. The statement lint (R2) has to decide
   what counts as a budget. Its rule, as I propose it: a constant reached
   from `Holds` (through the project's own definitions; core and library
   modules are not entered) is a budget if its name or one of its binder
   names contains `fuel` or `budget`, or if it is listed in
   `budgetNames`. The field lets a project name a budget the heuristic
   misses. Without it, R2 is the name heuristic alone.

## Toolchain (for your decision)

Proposal: pin `lean-toolchain` at **v4.31.0** (the older of the two) and
check every change on both v4.31.0 and v4.33.0. A Lake dependency is
compiled with the consumer's toolchain, so the pin matters only for building
lean-certify by itself; the library uses only core `Lean` (metaprogramming
API for the attribute and the lints), and drift in that API between versions
is the risk. Consequence: I cannot use any core API added after v4.31. Both
versions build the current files unchanged.

## A finding from the R3 lint (for your decision)

Since some Lean 4 release, well-founded recursion on a **`Nat`-valued**
measure compiles to `WellFounded.Nat.fix`, a fuelled `Nat.rec` with fuel
`measure x + 1`. It *does* reduce in the kernel: `by decide +kernel` proves
`wfLog 8 = 3` for a `termination_by n` definition (v4.31.0, measured). Only
lexicographic and other non-`Nat` measures go through `WellFounded.fix` and
a `._unary` auxiliary, which is what R3 was written against. The lint as built
follows R3 as decided and rejects `WellFounded.Nat.fix` too, with its own
message ("reduces in the kernel, but it is not structural"). Whether to
admit it is a statement-level choice for you. I would keep it rejected:
the measure is then evaluated at run time, which is the R1/R2 hazard.
