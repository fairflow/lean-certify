/-
# Lints: structural recursion (R3), domain materialisation (R1), axiom pin (R4)

`docs/outline.md` §6. Each lint is a *constant walk*: starting from a
declaration it follows the values of the definitions it reaches (the
evaluation path; theorem values are proofs and are not entered), and
reports any constant on a rule's list, with the chain that reaches it.

* `#certify_structural f` (R3, an error): `f`'s evaluation path (for a
  `Certifier` or `Engine`, that of its `check` functions only) must not
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
* `#certify_statement K` (R2, an error): the property `Holds` of the
  `Certifier` or `Engine` `K` mentions no budget. A constant reached from
  `Holds` (through the project's own definitions; library modules are not
  entered) is a budget if a component of its name, or one of the binder
  names in its type, contains `fuel` or `budget` (any case), or if it is
  listed in `Harness.config.budgetNames`. A measure in the theory itself
  (a height index of an inductive) is allowed: inductives are not entered.
* `#certify_axioms f` (R4, an error): the axioms of `f` lie within
  `Harness.config.axioms`, plus the exceptions it names for `f`.
-/
import LeanCertify.Certifier
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

/-- Breadth-first constant walk from the constants `seeds`, on behalf of
`root` (which is not itself checked). `bad n` says why `n` breaks the rule,
if it does; a bad constant is reported and not entered. `enter n` decides
whether the walk descends into `n`. Returns each offender with the chain
from `root` to it. -/
def walkFrom (env : Environment) (root : Name) (seeds : Array Name)
    (bad : Name → Option String) (enter : Name → Bool) :
    Array (Name × String × List Name) := Id.run do
  let mut parent : NameMap Name := {}
  let mut seen : NameSet := NameSet.empty.insert root
  let mut queue : Array Name := #[]
  for d in seeds do
    unless seen.contains d do
      seen := seen.insert d; parent := parent.insert d root; queue := queue.push d
  let mut i := 0
  let mut out := #[]
  -- `queue` only grows by constants not yet seen, so this terminates.
  while h : i < queue.size do
    let n := queue[i]
    i := i + 1
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

/-- The walk from a constant's own evaluation dependencies. -/
def walk (env : Environment) (root : Name) (bad : Name → Option String)
    (enter : Name → Bool) : Array (Name × String × List Name) :=
  walkFrom env root (evalDeps env root) bad enter

/-- The constants on the evaluation path of a `Certifier` (its `check`) or
an `Engine` (both `check`s); `none` for any other constant. Only these are
on the evaluation path: `sound` is a proof and `produce` is untrusted. A
certifier may be generic: its leading parameters are opened first. -/
def checkTerms (n : Name) : MetaM (Option (Array Name)) := do
  let ci ← getConstInfo n
  forallTelescopeReducing ci.type fun xs ty => do
    let k := mkAppN (mkConst n (ci.levelParams.map mkLevelParam)) xs
    let ty ← whnf ty
    let proj (c : Expr) : MetaM (Array Name) := do
      return (← whnf (← mkAppM ``Certify.Certifier.check #[c])).getUsedConstants
    match ty.getAppFn.constName? with
    | some ``Certify.Certifier => return some (← proj k)
    | some ``Certify.Engine =>
      return some ((← proj (← mkAppM ``Certify.Engine.yes #[k])) ++
                   (← proj (← mkAppM ``Certify.Engine.no #[k])))
    | _ => return none

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

/-- The panic functions. `panicCore msg` is `default` (Init/Prelude.lean,
v4.31.0 and v4.33.0): the message is discarded, and the other three only
build that message, so the kernel never evaluates it. Their values reach
`String.Internal.append` (opaque) and `Nat.repr` (`@[implemented_by]`)
through the message, which would otherwise flag every checker that uses
`xs[i]?`: the walk enters the whole `GetElem?` instance, `get!` included. -/
def panicLeaves : List Name :=
  [``panicCore, ``panic, ``panicWithPos, ``panicWithPosWithDecl]

/-- The R3 offenders reachable from `seeds`, on behalf of `n`. -/
def structuralOffenders (env : Environment) (n : Name) (seeds : Array Name) :
    Array (Name × String × List Name) :=
  walkFrom env n seeds (structuralOffence env)
    (fun c => !kernelNatOps.contains c && !panicLeaves.contains c)

/-! ### R1: domain materialisation -/

/-- Constants that count or build a finite domain. -/
def domainConsts : List Name :=
  [`Finset.card, `Finset.powerset, `Finset.product, `Fintype.card, `Finset.univ]

/-- The R1 reports for `n`. -/
def domainOffenders (env : Environment) (n : Name) : Array (Name × String × List Name) :=
  walk env n
    (fun c => if domainConsts.contains c then some "materialises or counts a domain" else none)
    (fun c => !isLibrary env c)

/-! ### R2: no budget in the statement -/

/-- Does a name mention a budget? -/
def budgetish (n : Name) : Bool :=
  n.components.any fun c => match c with
    | .str _ s => let l := s.toLower; (l.splitOn "fuel").length > 1 || (l.splitOn "budget").length > 1
    | _ => false

/-- The binder names of a type's leading `∀`s. -/
partial def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | .mdata _ e => binderNames e
  | _ => []

/-- Why constant `c` counts as a budget, if it does. -/
def budgetOffence (env : Environment) (extra : List Name) (c : Name) : Option String :=
  if extra.contains c then some "listed in Harness.config.budgetNames"
  else if budgetish c then some "its name mentions a budget"
  else match env.find? c with
    | some ci =>
      match (binderNames ci.type).find? budgetish with
      | some b => some s!"it takes a budget argument `{b}`"
      | none => none
    | none => none

/-- The `Holds` argument of a `Certifier` or `Engine` constant's type. -/
def holdsOf (n : Name) : MetaM Expr := do
  let ci ← getConstInfo n
  -- A generic certifier's parameters are opened; `Holds` may mention them,
  -- which is harmless here: only its constants are read.
  forallTelescopeReducing ci.type fun _ ty => do
    let ty ← whnf ty
    match ty.getAppFn.constName?, ty.getAppArgs with
    | some ``Certify.Certifier, #[_, _, h] => return h
    | some ``Certify.Engine, #[_, _, _, h] => return h
    | _, _ => throwError "{.ofConstName n} is not a Certify.Certifier or Certify.Engine"

/-- The R2 offenders of `Holds`. A synthetic root stands for `Holds` itself. -/
def statementOffenders (env : Environment) (extra : List Name) (holds : Expr) :
    Array (Name × String × List Name) := Id.run do
  let root := `«Holds»
  let mut out := #[]
  -- Binder names inside `Holds` itself.
  let rec go : Expr → Array Name → Array Name
    | .lam n t b _, acc => go b (go t (acc.push n))
    | .forallE n t b _, acc => go b (go t (acc.push n))
    | .app f a, acc => go a (go f acc)
    | .mdata _ e, acc => go e acc
    | .letE n t v b _, acc => go b (go v (go t (acc.push n)))
    | _, acc => acc
  for b in go holds #[] do
    if budgetish b then out := out.push (b, "a binder of `Holds` names a budget", [root])
  for c in holds.getUsedConstants do
    if let some why := budgetOffence env extra c then
      out := out.push (c, why, [root, c])
    else if !isLibrary env c then
      for (d, why, chain) in walk env c (budgetOffence env extra) (!isLibrary env ·) do
        out := out.push (d, why, root :: chain)
  return out

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
    let seeds ← liftTermElabM do
      match ← checkTerms n with
      | some cs => return cs
      | none => return evalDeps (← getEnv) n
    let env ← getEnv
    let offs := structuralOffenders env n seeds
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

/-- R2: no budget in the statement of the certifier or engine `K`. -/
syntax (name := certifyStatement) "#certify_statement " ident : command

@[command_elab certifyStatement] def elabStatement : CommandElab
  | `(#certify_statement $id) => do
    let n ← resolve id
    let cfg ← liftTermElabM Harness.readConfig
    let holds ← liftTermElabM <| holdsOf n
    let env ← getEnv
    let offs := statementOffenders env cfg.budgetNames holds
    if offs.isEmpty then
      logInfo m!"R2 passes: the property of {.ofConstName n} mentions no budget"
    else
      logErrorAt id m!"R2 fails: the property of {.ofConstName n} mentions a budget \
        ({offs.size} site(s)); a budget belongs in `produce` or `Engine.Complete`:\
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
