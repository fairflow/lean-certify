/-
# Lints: structural recursion (R3), domain materialisation (R1), axiom pin (R4)

`docs/outline.md` §6. Each lint is a *constant walk*: starting from a
declaration it follows the values of the definitions it reaches (the
evaluation path; theorem values are proofs and are not entered), and
reports any constant on a rule's list, with the chain that reaches it.

* `#certify_structural f` (R3, an error): `f`'s evaluation path must not
  reach `WellFounded.fix`, a `._unary`/`._binary` auxiliary of well-founded
  recursion, `WellFounded.Nat.fix` (which does reduce, but is not
  structural; see `docs/v1-report.md`), an opaque constant (which is what `partial` produces), or a
  declaration with `@[implemented_by]`. The walk enters every module,
  core included, since the kernel unfolds them all.
* `#certify_domain f` (R1, reporting only, decision 8): `f`'s evaluation
  path must not count or build the domain of a measure (`Finset.card`,
  `Finset.powerset`, `Finset.product`, `Fintype.card`). The walk enters
  only the project's own modules; library constants are checked by name
  and not entered. Silenced by `Harness.config.lintDomain := false`, or per
  declaration by `@[harness silenceDomainLint := true]`.
* `#certify_axioms f` (R4, an error): the axioms of `f` lie within
  `Harness.config.axioms`, plus the exceptions it names for `f`.
-/
import LeanCertify.Config

open Lean Elab Command Meta

namespace Certify.Lint

/-- Library prefixes the domain lint does not enter. -/
def libraryPrefixes : List Name :=
  [`Init, `Std, `Lean, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible]

/-- The module a constant comes from; `none` for the current file. -/
def moduleOf (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.bind fun i => env.header.moduleNames[i.toNat]?

/-- Is `n` declared in a library module (not the project's)? -/
def isLibrary (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | none => false
  | some m => libraryPrefixes.any (·.isPrefixOf m)

/-- The constants a constant's evaluation depends on: the value of a
definition, nothing for anything else (theorems, axioms, inductives,
constructors, recursors, opaque constants). -/
def evalDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.defnInfo d) => d.value.getUsedConstants
  | _ => #[]

/-- Breadth-first constant walk from `root`. `bad n` says why `n` breaks
the rule, if it does; a bad constant is reported and not entered. `enter n`
decides whether the walk descends into `n`. Returns each offender with the
chain from `root` to it. -/
def walk (env : Environment) (root : Name) (bad : Name → Option String)
    (enter : Name → Bool) : Array (Name × String × List Name) := Id.run do
  let mut parent : NameMap Name := {}
  let mut seen : NameSet := NameSet.empty.insert root
  let mut queue : Array Name := #[root]
  let mut i := 0
  let mut out := #[]
  -- `queue` only grows by constants not yet seen, so this terminates.
  while h : i < queue.size do
      let n := queue[i]
      i := i + 1
      if n != root then
        if let some why := bad n then
          let mut chain := [n]
          let mut cur := n
          for _ in [0:queue.size] do
            match parent.find? cur with
            | some p => chain := p :: chain; cur := p
            | none => break
          out := out.push (n, why, chain)
          continue
        unless enter n do continue
      for d in evalDeps env n do
        unless seen.contains d do
          seen := seen.insert d
          parent := parent.insert d n
          queue := queue.push d
  return out

/-! ### R3: structural recursion -/

/-- The `Nat` operations the Lean kernel itself evaluates on literals (GMP
acceleration): exactly the binary cases of `type_checker::reduce_nat` in
`src/kernel/type_checker.cpp`, identical at v4.31.0 and v4.33.0, e.g.
<https://github.com/leanprover/lean4/blob/v4.31.0/src/kernel/type_checker.cpp>
(lines 622–635). `Nat.log2` is not among them. Some are defined by
well-founded recursion (`Nat.land` through `Nat.bitwise._unary`), but on
literals the kernel never unfolds them, so the R3 walk treats these and only
these as leaves. This is not an exemption for fast well-founded
definitions: a user's own is still rejected (`LeanCertifyTest/Lint.lean`). -/
def kernelNatOps : List Name :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.gcd, ``Nat.beq,
   ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight,
   ``Nat.pow]

/-- Why `n` blocks kernel reduction, if it does. -/
def structuralOffence (env : Environment) (n : Name) : Option String :=
  if n == ``WellFounded.fix || n == ``WellFounded.fixF then
    some "well-founded recursion (does not reduce in the kernel)"
  else if n == ``WellFounded.Nat.fix then
    some "well-founded recursion on a `Nat` measure: it reduces in the kernel \
      (fuel `measure + 1`), but it is not structural"
  else if n.isStr && (n.getString! == "_unary" || n.getString! == "_binary") then
    some "auxiliary of a definition by well-founded recursion"
  else if (Compiler.implementedByAttr.getParam? env n).isSome then
    some "@[implemented_by]: the compiled code is not the definition"
  else match env.find? n with
    | some (.opaqueInfo _) => some "opaque (a `partial def` or `opaque`): no value to reduce"
    | _ => none

/-- The R3 offenders reachable from `n`. -/
def structuralOffenders (env : Environment) (n : Name) : Array (Name × String × List Name) :=
  walk env n (structuralOffence env) (!kernelNatOps.contains ·)

/-! ### R1: domain materialisation -/

/-- Constants that count or build a finite domain. -/
def domainConsts : List Name :=
  [`Finset.card, `Finset.powerset, `Finset.product, `Fintype.card, `Finset.univ]

/-- The R1 reports for `n`. -/
def domainOffenders (env : Environment) (n : Name) : Array (Name × String × List Name) :=
  walk env n
    (fun c => if domainConsts.contains c then some "materialises or counts a domain" else none)
    (fun c => !isLibrary env c)

/-! ### Commands -/

private def resolve (id : Ident) : CommandElabM Name :=
  liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def render (env : Environment) (offs : Array (Name × String × List Name)) :
    MessageData := Id.run do
  let mut m := m!""
  for (c, why, chain) in offs do
    let origin := (moduleOf env c).map toString |>.getD "this file"
    m := m ++ m!"\n• {.ofConstName c} [{origin}]: {why}\n    via {chain}"
  return m

/-- R3: `f`'s evaluation path is structural. An error otherwise. -/
syntax (name := certifyStructural) "#certify_structural " ident : command

@[command_elab certifyStructural] def elabStructural : CommandElab
  | `(#certify_structural $id) => do
    let n ← resolve id
    let env ← getEnv
    let offs := structuralOffenders env n
    if offs.isEmpty then
      logInfo m!"R3 passes: the evaluation path of {.ofConstName n} is structural"
    else
      logErrorAt id m!"R3 fails: the evaluation path of {.ofConstName n} reaches \
        {offs.size} constant(s) R3 forbids:{render env offs}"
  | _ => throwUnsupportedSyntax

/-- R1: report domain materialisation on `f`'s evaluation path. A warning,
never an error. -/
syntax (name := certifyDomain) "#certify_domain " ident : command

@[command_elab certifyDomain] def elabDomain : CommandElab
  | `(#certify_domain $id) => do
    let n ← resolve id
    let env ← getEnv
    let cfg ← liftTermElabM Harness.readConfig
    if !cfg.lintDomain then
      logInfo m!"R1 skipped: Harness.config.lintDomain is false"; return
    if (Harness.certifierConfigOf env n).silenceDomainLint then
      logInfo m!"R1 skipped: {.ofConstName n} has @[harness silenceDomainLint := true]"; return
    let offs := domainOffenders env n
    if offs.isEmpty then
      logInfo m!"R1: nothing to report on {.ofConstName n}"
    else
      logWarningAt id m!"R1 reports: the evaluation path of {.ofConstName n} counts or \
        builds a domain at run time ({offs.size} site(s)); pass a cheap bound instead:\
        {render env offs}"
  | _ => throwUnsupportedSyntax

/-- R4: the axioms of `f` lie within the project's allow-list (plus the
exceptions it names for `f`). -/
syntax (name := certifyAxioms) "#certify_axioms " ident : command

@[command_elab certifyAxioms] def elabAxioms : CommandElab
  | `(#certify_axioms $id) => do
    let n ← resolve id
    let cfg ← liftTermElabM Harness.readConfig
    let extra := (cfg.axiomExceptions.find? (·.1 == n)).map (·.2) |>.getD []
    let allowed := cfg.axioms ++ extra
    let axs ← collectAxioms n
    let outside := axs.filter (!allowed.contains ·)
    if outside.isEmpty then
      logInfo m!"R4 passes: {.ofConstName n} depends on {axs.toList} ⊆ {allowed}"
    else
      logErrorAt id m!"R4 fails: {.ofConstName n} depends on {outside.toList}, \
        outside the allow-list {allowed}"
  | _ => throwUnsupportedSyntax

end Certify.Lint
