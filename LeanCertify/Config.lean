/-
# Project and per-certifier configuration

`docs/outline.md` §8 (decisions 12 and 15). A project supplies one constant
`Harness.config : Harness.Config` in a Lean file, listing only the fields it
changes; the lints read it from the environment. Per-certifier overrides are
the attribute `@[harness …]` on a `Certifier` or `Engine` declaration. The
axiom allow-list has no per-certifier override, deliberately.

The configuration is ordinary data that never enters a proof: it is
untrusted, and the lints evaluate it with compiled code. JSON for non-Lean
tools is generated from it (`toJson Harness.config`), never read back.
-/
import Lean

open Lean

namespace Harness

/-- P2: where the checker is evaluated. V1 supports `kernel` only. -/
inductive Route | kernel | native | external
  deriving Repr, DecidableEq, ToJson, FromJson

/-- P10: where the certificate is spliced in. -/
inductive Splice | factFile | tactic
  deriving Repr, DecidableEq, ToJson, FromJson

/-- P12: whether certificates are committed or regenerated per build. -/
inductive Storage | committed | regenerated
  deriving Repr, DecidableEq, ToJson, FromJson

/-- Project-wide settings, one constant `Harness.config` per project. -/
structure Config where
  /-- P2. -/
  route : Route := .kernel
  /-- P3, R4: the axiom allow-list. -/
  axioms : List Name := [``propext, ``Quot.sound]
  /-- P3: named declarations allowed further axioms. -/
  axiomExceptions : List (Name × List Name) := []
  /-- P11: rows per `decide` when chunking; `none` means one literal. -/
  chunkSize : Option Nat := none
  /-- P12. -/
  storage : Storage := .committed
  /-- R5: how many times a `flag` is rerun at a raised budget. -/
  flagReruns : Nat := 2
  /-- R5: the budget multiplier per raise. -/
  budgetFactor : Nat := 4
  /-- R7: wall-clock deadline per producer run. -/
  deadlineSec : Nat := 600
  /-- R8: a kernel check slower than this is reported. -/
  kernelTimeFlagSec : Nat := 180
  /-- R1: run the domain-materialisation lint (reporting only). -/
  lintDomain : Bool := true
  /-- R2: further constants the statement lint treats as budgets, beyond
  those whose name or binder mentions fuel or a budget. -/
  budgetNames : List Name := []
  /-- R11: run `lean4checker` as a test. -/
  lean4checker : Bool := false
  deriving Repr, ToJson, FromJson

/-- Per-certifier overrides, attached by `@[harness …]`. -/
structure CertifierConfig where
  /-- P10. -/
  splice : Splice := .factFile
  /-- R6: run the untrusted minimiser before the splice. -/
  minimise : Bool := true
  /-- P11 override. -/
  chunkSize : Option Nat := none
  /-- R7 override. -/
  deadlineSec : Option Nat := none
  /-- R1: silence the domain lint on this declaration. -/
  silenceDomainLint : Bool := false
  deriving Repr, ToJson, FromJson, Inhabited

/-- The per-declaration overrides, persisted across modules. -/
initialize certifierConfigExt :
    SimplePersistentEnvExtension (Name × CertifierConfig) (NameMap CertifierConfig) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, c) => m.insert n c
    addImportedFn := fun ess =>
      ess.foldl (init := {}) fun m es => es.foldl (init := m) fun m (n, c) => m.insert n c
  }

/-- The overrides attached to `n`, or the defaults. -/
def certifierConfigOf (env : Environment) (n : Name) : CertifierConfig :=
  (certifierConfigExt.getState env).find? n |>.getD {}

/-- `@[harness splice := .tactic, minimise := false]`. Each field is
elaborated against `CertifierConfig`; an unknown field is an error. -/
syntax (name := harness) "harness" (ppSpace ident " := " term),* : attr

/-- The project's `Harness.config` if it declares one, else the defaults.
The constant is evaluated, so it must be defined in an imported module or
earlier in the current one. -/
def readConfig : MetaM Config := do
  let n := `Harness.config
  if (← getEnv).contains n then
    unsafe evalConstCheck Config ``Config n
  else
    return {}

end Harness

open Elab Term Meta in
initialize registerBuiltinAttribute {
  name := `harness
  descr := "per-certifier overrides of the Lean certify configuration"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "@[harness] must be global"
    let `(attr| harness $[$fs := $vs],*) := stx | throwUnsupportedSyntax
    let fields := fs.zip vs
    let fieldNames := getStructureFields (← getEnv) ``Harness.CertifierConfig
    for (f, _) in fields do
      unless fieldNames.contains f.getId do
        throwErrorAt f "unknown field '{f.getId}' of Harness.CertifierConfig \
          (the axiom list has no per-certifier override)"
    let inst ← `({ $[$fs:ident := $vs],* : Harness.CertifierConfig })
    let cfg ← MetaM.run' <| TermElabM.run' do
      let e ← elabTermEnsuringType inst (mkConst ``Harness.CertifierConfig)
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      unsafe evalExpr Harness.CertifierConfig (mkConst ``Harness.CertifierConfig) e
    modifyEnv (Harness.certifierConfigExt.addEntry · (decl, cfg))
}
