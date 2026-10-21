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
  structural; see `docs/v1-report.md`), `Lean.Order.fix` (what
  `partial_fixpoint` produces: a least fixpoint, not kernel-reducible; such a
  definition belongs in `produce`, or in `Holds` with a certificate checked
  against it), an opaque constant (which is what `partial` produces), or an
  axiom that is not a proposition (`Classical.choice`, `sorryAx`: no value to
  reduce; v0.3.1). Propositional axioms (`propext`, `Quot.sound`) never block
  the kernel and are not reported; proofs are not walked. A declaration with `@[implemented_by]` is
  information under `route := .kernel` (the kernel reduces its reference
  definition; v0.2) and an error under any other route. The walk enters every module,
  core included, since the kernel unfolds them all; under the kernel route it
  also enters an `@[implemented_by]` definition, whose value is what the
  kernel reduces (v0.2.1).
  **On a theorem** (v0.2.1, `docs/v0.2.1-statements.md`) the walk starts
  from what its proof decides by evaluation: each `of_decide_eq_true`
  (or `of_decide_eq_false`, `eq_true_of_decide`, `eq_false_of_decide`)
  applied to a reflexivity proof, in the proof or in an auxiliary theorem
  generated for it (`_proof_1_1`, `_auxLemma`, …), seeds the walk with the
  definitions in the decided proposition and its `Decidable` instance (a
  `Certifier` or `Engine` among them by its `check` functions only). A
  theorem whose proof decides nothing is an error ("nothing to walk"), never
  a pass. What R3 forbids there is an error (`decidedOffenceIsError`).
  `#certify_structural f allow c "reason", …` downgrades to a warning what R3
  forbids on the path below each named constant `c`; an allowance below
  which R3 forbids nothing, or which is not on the path, is an error.
* `#certify_domain f` (R1, reporting only, decision 8): `f`'s evaluation
  path must not count or build the domain of a measure (`Finset.card`,
  `Finset.powerset`, `Finset.product`, `Fintype.card`). The walk enters
  only the project's own modules; library constants are checked by name
  and not entered. Silenced by `Harness.config.lintDomain := false`, or per
  declaration by `@[harness silenceDomainLint := true]`. On a theorem it
  walks what the proof decides by evaluation, as R3 does; a theorem that
  decides nothing is an error ("nothing to walk").
* `#certify_statement K` (R2, an error): the property `Holds` of the
  `Certifier` or `Engine` `K` mentions no budget. A constant reached from
  `Holds` (through the project's own definitions; library modules are not
  entered) is a budget if a component of its name, or one of the binder
  names in its type, contains `fuel` or `budget` (any case), or if it is
  listed in `Harness.config.budgetNames`. A measure in the theory itself
  (a height index of an inductive) is allowed: inductives are not entered.
* The **R4 linter** (an error, automatic since v0.1.3): after every
  command, each newly declared constant whose type is a `Certifier` or an
  `Engine` (under its parameters) has its axioms checked against
  `Harness.config`, as `#certify_axioms` would. A `sound` proof that pulls
  in `Classical.choice` (by `tauto`, say) then fails at its declaration.
* `#certify_axioms f` (R4, an error): the axioms of `f` lie within
  `Harness.config.axioms`, plus the exceptions it names for `f`.
* **The pin does not see the producer** (Matthew, 2026-10-21: only certified
  results need a pin). For an `Engine`, a `Prover` or a `Disprover`, R4
  checks its type and its certifiers; `produce` is untrusted, never evaluated
  by the kernel, and may reach `Classical.choice` (a `partial_fixpoint`
  search does). A result stated with the named certifier (`K.verdict`, not
  `E.yes.verdict`) does not mention the producer at all.
  **`sorryAx` fails everywhere**, the producer included, whatever the
  allow-list says.
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

/-- The certifier fields of a bundle that carries an untrusted producer:
an `Engine` (`yes`, `no`), a `Prover` or a `Disprover` (`certifier`;
declared in `LeanCertify.Decider`, which imports this module's imports but
not this module, hence the unchecked names). -/
def bundleCertifiers : List (Name × List Name) :=
  [(``Certify.Engine, [``Certify.Engine.yes, ``Certify.Engine.no]),
   (`Certify.Prover, [`Certify.Prover.certifier]),
   (`Certify.Disprover, [`Certify.Disprover.certifier])]

/-- R4's two axiom sets for `n`: those the pin covers, and all of them. For a
bundle with a producer (`bundleCertifiers`) the pin covers its type and its
certifiers, not `produce` (Matthew, 2026-10-21: only certified results need a
pin). For anything else both are `collectAxioms n`. -/
def pinnedAxioms (n : Name) : MetaM (Array Name × Array Name) := do
  let all ← collectAxioms n
  let ci ← getConstInfo n
  let parts? ← forallTelescopeReducing ci.type fun xs ty => do
    let ty ← whnf ty
    let some fields := ty.getAppFn.constName?.bind (List.lookup · bundleCertifiers)
      | return none
    let k := mkAppN (mkConst n (ci.levelParams.map mkLevelParam)) xs
    let mut cs := ci.type.getUsedConstants
    for f in fields do
      cs := cs ++ (← whnf (← mkAppM f #[k])).getUsedConstants
    return some cs
  let some cs := parts? | return (all, all)
  let mut pinned : Array Name := #[]
  for c in cs do
    for a in ← collectAxioms c do
      unless pinned.contains a do pinned := pinned.push a
  return (pinned, all)

/-- R4's verdict on `n`, given the allow-list: `none` if it passes, else the
error. `sorryAx` is never allowed, whatever the allow-list says, and fails
even when only the producer reaches it. `what` names `n` in the message. -/
def axiomFailure (n : Name) (what : MessageData) (pinned all : Array Name)
    (allowed : List Name) (suffix : MessageData := m!"") : Option MessageData :=
  let outside := pinned.filter fun a => a == ``sorryAx || !allowed.contains a
  if !outside.isEmpty then
    some m!"R4 fails: {what} depends on {outside.toList}, outside the allow-list {allowed}{suffix}"
  else if all.contains ``sorryAx then
    some m!"R4 fails: the producer of {.ofConstName n} depends on sorryAx: \
      a `sorry` fails everywhere, the producer included"
  else none

/-- For a failed pin on `n`: each bundle named in `n`'s value whose producer,
not its certifiers, brings in one of the axioms `excess`. A result stated as
`E.yes.verdict s c` names the engine `E`, and with it the producer. -/
def producerHint (n : Name) (excess : Array Name) : MetaM MessageData := do
  let some v := (← getEnv).find? n |>.bind (·.value? (allowOpaque := true)) | return m!""
  let mut out := m!""
  for c in v.getUsedConstants do
    let (pinned, all) ← pinnedAxioms c
    if excess.any fun a => all.contains a && !pinned.contains a then
      out := out ++ m!"\n  they enter through the producer of {.ofConstName c}: state the result \
        with the named certifier (`K.verdict`, not `E.yes.verdict`), whose term does not \
        mention the producer"
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

/-- Does `n` carry `@[implemented_by]`? -/
def isImplementedBy (env : Environment) (n : Name) : Bool :=
  (Compiler.implementedByAttr.getParam? env n).isSome

/-- Is `t`, the type of an axiom, a proposition? Read off syntactically: the
body under the leading `∀`s is headed by a constant whose type ends in
`Prop` (`Eq`, `True`, …), or by a bound variable whose binder type is `Prop`.
Anything else counts as data, which is the cautious answer for R3. Covers
`propext`, `Quot.sound`, `Lean.ofReduceBool` (propositions) and
`Classical.choice`, `sorryAx` (data). -/
def isPropType (env : Environment) (t : Expr) : Bool :=
  go #[] t
where
  endsInProp : Expr → Bool
    | .forallE _ _ b _ => endsInProp b
    | .mdata _ e => endsInProp e
    | e => e == .sort .zero
  go (ctx : Array Expr) : Expr → Bool
    | .forallE _ d b _ => go (ctx.push d) b
    | .mdata _ e => go ctx e
    | e => match e.getAppFn with
      | .const c _ => match env.find? c with
        | some ci => endsInProp ci.type
        | none => false
      | .bvar i =>
        if i < ctx.size then ctx[ctx.size - 1 - i]!.consumeMData == .sort .zero else false
      | _ => false

/-- Why `n` blocks kernel reduction, if it does. -/
def structuralOffence (env : Environment) (n : Name) : Option String :=
  if n == ``WellFounded.fix || n == ``WellFounded.fixF then
    some "well-founded recursion (does not reduce in the kernel)"
  else if n == ``WellFounded.Nat.fix then
    some "well-founded recursion on a `Nat` measure: it reduces in the kernel \
      (fuel `measure + 1`), but it is not structural"
  else if n == ``Lean.Order.fix then
    some "partial_fixpoint (a least fixpoint): not kernel-reducible; use it in `produce`, \
      or state facts about it in `Holds` and check them with a certificate"
  else if n.isStr && (n.getString! == "_unary" || n.getString! == "_binary") then
    some "auxiliary of a definition by well-founded recursion"
  else if isImplementedBy env n then
    some "@[implemented_by]: the compiled code is not the definition"
  else if n == ``sorryAx then
    some "a `sorry`: no value to reduce"
  else match env.find? n with
    | some (.opaqueInfo _) => some "opaque (a `partial def` or `opaque`): no value to reduce"
    | some (.axiomInfo ai) =>
      if isPropType env ai.type then none
      else some "an axiom that is not a proposition: no value to reduce"
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

/-! ### R3 and R1 on theorems: what a proof decides by evaluation (v0.2.1) -/

/-- D2, decided by the project's manager on Matthew's statement that
termination arguments are what most need the certified route (2026-10-14):
what R3 forbids on a theorem's decided content is an error. Set this to
`false` to make it a warning. A definition's R3 offences are errors either
way. -/
def decidedOffenceIsError : Bool := true

/-- The lemmas that carry a Boolean decision to its proposition. Each takes
the proposition `p`, its `Decidable p` instance and an equation
`decide p = b`, in that order. Given a reflexivity proof of the equation,
the kernel evaluates `decide p`: `decide` leaves `of_decide_eq_true`,
`simp (config := {decide := true})` leaves `eq_true_of_decide`. -/
def decideLemmas : List Name :=
  [``of_decide_eq_true, ``of_decide_eq_false, ``eq_true_of_decide, ``eq_false_of_decide]

/-- Is `c` an auxiliary theorem generated for a proof in `root`'s module: a
theorem of the same module (other than `root`) whose name, private prefix
removed, is an implementation detail (`t._proof_1_1` from `decide +kernel`,
`_auxLemma`, `proof_1`)? Its proof was checked with `root`'s, so what it
decides is `root`'s. A user-named theorem is checked on its own and is not
entered. -/
def isAuxTheorem (env : Environment) (root c : Name) : Bool :=
  c != root && moduleOf env c == moduleOf env root &&
    (privateToUserName c).isInternalDetail &&
    match env.find? c with
    | some (.thmInfo _) => true
    | _ => false

/-- Is `e` a proof by reflexivity (`Eq.refl`, `rfl`, under `id` and
metadata, or an auxiliary theorem whose value is one)? Only then does the
kernel evaluate the decision; a hypothesis `h : decide p = true` is not
evaluated. -/
partial def isReflProof (env : Environment) (root : Name) (e : Expr) : Bool :=
  let e := e.consumeMData
  match e.getAppFn with
  | .const ``Eq.refl _ | .const ``rfl _ => true
  | .const ``id _ => e.getAppNumArgs == 2 && isReflProof env root e.appArg!
  | .const c _ =>
    e.getAppNumArgs == 0 && isAuxTheorem env root c &&
      match env.find? c with
      | some (.thmInfo ti) => isReflProof env root ti.value
      | _ => false
  | _ => false

/-- The decisions the proof of the theorem `root` evaluates: the proposition
and instance `(p, inst)` of each decide lemma (`decideLemmas`) applied to a
reflexivity proof, in `root`'s proof or in an auxiliary theorem it uses
(`isAuxTheorem`), each auxiliary visited once. Theorems are otherwise not
entered (proof irrelevance). -/
def decidedSites (root : Name) : MetaM (Array (Expr × Expr)) := do
  let env ← getEnv
  let sites ← IO.mkRef (#[] : Array (Expr × Expr))
  let pending ← IO.mkRef (#[root] : Array Name)
  let mut done : NameSet := {}
  -- Each pass takes one theorem; a theorem is visited at most once and the
  -- auxiliaries of a module are finitely many, so this terminates.
  repeat
    let some t := (← pending.get).back? | break
    pending.modify (·.pop)
    if done.contains t then continue
    done := done.insert t
    let some (.thmInfo ti) := env.find? t | continue
    ti.value.forEach' fun e => do
      if let .const c _ := e.getAppFn then
        if decideLemmas.contains c && e.getAppNumArgs ≥ 3 &&
            isReflProof env root (e.getArg! 2) then
          sites.modify (·.push (e.getArg! 0, e.getArg! 1))
        if isAuxTheorem env root c then
          pending.modify (·.push c)
      return true
  -- An over-applied lemma is met once per prefix of its arguments.
  return (← sites.get).foldl (init := #[]) fun acc s => if acc.contains s then acc else acc.push s

/-- Where the walk of a decided theorem starts: the definitions and opaque
constants of each decided proposition and its instance, each with its parent
in the chain. A `Certifier` or `Engine` constant among them is replaced by
its `check` functions (`checkTerms`), as when it is the root: its producer is
untrusted and never evaluated by the kernel. Such a constant is returned as a
link, so that chains pass through it. -/
def decidedSeeds (root : Name) (sites : Array (Expr × Expr)) :
    MetaM (Array (Name × Name) × Array (Name × Name)) := do
  let env ← getEnv
  let mut links := #[]
  let mut seeds := #[]
  let mut seen : NameSet := {}
  for (p, inst) in sites do
    for c in p.getUsedConstants ++ inst.getUsedConstants do
      if seen.contains c then continue
      seen := seen.insert c
      match env.find? c with
      | some (.defnInfo _) =>
        match ← checkTerms c with
        | some cs =>
          links := links.push (c, root)
          seeds := seeds ++ cs.map (·, c)
        | none => seeds := seeds.push (c, root)
      | some (.opaqueInfo _) => seeds := seeds.push (c, root)
      | _ => pure ()
  return (links, seeds)

/-- How a walk treats a constant it reaches. -/
inductive Mark where
  /-- Reported, and not entered. -/
  | forbid (why : String)
  /-- Reported, and entered. -/
  | note (why : String)
  /-- Named by an allowance: reported, and not entered (walked separately). -/
  | allow

/-- Breadth-first constant walk on behalf of `root`. `links` are extra nodes
of the chain (seen, with their parent, not entered); `seeds` the constants it
starts from, each with its parent. Returns each marked constant with its mark
and the chain from `root` to it. Over the same seeds, unmarked links, and
with `forbid` for every offence, it is `walkFrom`. -/
def walkMarked (env : Environment) (root : Name) (links seeds : Array (Name × Name))
    (mark : Name → Option Mark) (enter : Name → Bool) :
    Array (Name × Mark × List Name) := Id.run do
  let mut parent : NameMap Name := {}
  let mut seen : NameSet := NameSet.empty.insert root
  let mut queue : Array Name := #[]
  for (l, p) in links do
    unless seen.contains l do
      seen := seen.insert l; parent := parent.insert l p
  for (d, p) in seeds do
    unless seen.contains d do
      seen := seen.insert d; parent := parent.insert d p; queue := queue.push d
  let mut i := 0
  let mut out := #[]
  let bound := queue.size + links.size + 1
  -- `queue` only grows by constants not yet seen, so this terminates.
  while h : i < queue.size do
    let n := queue[i]
    i := i + 1
    let m := mark n
    if let some mk := m then
      let mut chain := [n]
      let mut cur := n
      for _ in [0:queue.size + bound] do
        match parent.find? cur with
        | some p => chain := p :: chain; cur := p
        | none => break
      out := out.push (n, mk, chain)
      match mk with
      | .note _ => pure ()
      | _ => continue
    unless enter n do continue
    for d in evalDeps env n do
      unless seen.contains d do
        seen := seen.insert d
        parent := parent.insert d n
        queue := queue.push d
  return out

/-- An R3 offence: the constant, why R3 forbids it, the chain to it. -/
abbrev Offence := Name × String × List Name

/-- The outcome of an R3 walk. -/
structure StructuralReport where
  /-- What R3 forbids, outside every allowance. -/
  errors : Array Offence := #[]
  /-- `@[implemented_by]` under the kernel route: information only. -/
  notes : Array Offence := #[]
  /-- What R3 forbids below an allowance, with the allowance. -/
  allowed : Array (Offence × Name) := #[]
  /-- Allowances not on the path. -/
  unreached : Array Name := #[]
  /-- Allowances on the path below which R3 forbids nothing. -/
  idle : Array Name := #[]

/-- R3 from `seeds` (with `links`, as in `walkMarked`), on behalf of `root`,
under `route`, with the allowances `allow`. The main walk stops at an allowed
constant; each allowed constant reached is then walked on its own, and what
R3 forbids below it is `allowed` rather than an error. -/
def structuralReport (env : Environment) (route : Harness.Route) (root : Name)
    (links seeds : Array (Name × Name)) (allow : List Name) : StructuralReport := Id.run do
  let markOf (c : Name) : Option Mark :=
    if allow.contains c then some .allow
    else match structuralOffence env c with
      | some why =>
        if route == .kernel && isImplementedBy env c then some (.note why)
        else some (.forbid why)
      | none => none
  let enter (c : Name) := !kernelNatOps.contains c && !panicLeaves.contains c
  let mut rep : StructuralReport := {}
  -- Allowed constants still to walk, with the chain to each.
  let mut todo : Array (Name × List Name) := #[]
  let mut reached : NameSet := {}
  let mut used : NameSet := {}
  for (c, mk, chain) in walkMarked env root links seeds markOf enter do
    match mk with
    | .forbid why => rep := { rep with errors := rep.errors.push (c, why, chain) }
    | .note why => rep := { rep with notes := rep.notes.push (c, why, chain) }
    | .allow => todo := todo.push (c, chain)
  -- Each allowed constant is walked once and pushes at most one entry per
  -- allowance, so there are at most `k + k * k` entries for `k` allowances.
  for _ in [0:allow.length * (allow.length + 1) + 1] do
    let some (a, chain) := todo.back? | break
    todo := todo.pop
    if reached.contains a then continue
    reached := reached.insert a
    -- The allowed constant itself may be what R3 forbids.
    match structuralOffence env a with
    | some why =>
      if route == .kernel && isImplementedBy env a then
        rep := { rep with notes := rep.notes.push (a, why, chain) }
      else
        rep := { rep with allowed := rep.allowed.push ((a, why, chain), a) }
        used := used.insert a
        continue
    | none => pure ()
    unless enter a do continue
    let below := walkMarked env a #[] ((evalDeps env a).map (·, a))
      (fun c => if c == a then none else markOf c) enter
    for (c, mk, sub) in below do
      let full := chain ++ sub.drop 1
      match mk with
      | .forbid why =>
        rep := { rep with allowed := rep.allowed.push ((c, why, full), a) }
        used := used.insert a
      | .note why =>
        unless rep.notes.any (·.1 == c) do
          rep := { rep with notes := rep.notes.push (c, why, full) }
      | .allow => todo := todo.push (c, full)
  for a in allow do
    if !reached.contains a then rep := { rep with unreached := rep.unreached.push a }
    else if !used.contains a then rep := { rep with idle := rep.idle.push a }
  return rep

/-- What a lint walks for the constant `n`. -/
inductive Origin where
  /-- From these constants (a definition's value, a certifier's checks). -/
  | value (seeds : Array Name)
  /-- From what a theorem's proof decides by evaluation. -/
  | decided (props : Array Expr) (links seeds : Array (Name × Name))
  /-- A theorem whose proof decides nothing: nothing to walk. -/
  | nothing

/-- The origin of a theorem's walk, or `none` if `n` is not a theorem. -/
def theoremOrigin? (n : Name) : MetaM (Option Origin) := do
  let some (.thmInfo _) := (← getEnv).find? n | return none
  let sites ← decidedSites n
  if sites.isEmpty then return some .nothing
  let (links, seeds) ← decidedSeeds n sites
  return some (.decided (sites.map (·.1) |>.foldl (init := #[]) fun acc p =>
    if acc.contains p then acc else acc.push p) links seeds)

/-! ### R1: domain materialisation -/

/-- Constants that count or build a finite domain. -/
def domainConsts : List Name :=
  [`Finset.card, `Finset.powerset, `Finset.product, `Fintype.card, `Finset.univ]

/-- The R1 reports for `n`. -/
def domainOffenders (env : Environment) (n : Name) : Array (Name × String × List Name) :=
  walk env n
    (fun c => if domainConsts.contains c then some "materialises or counts a domain" else none)
    (fun c => !isLibrary env c)

/-- The R1 reports for a decided theorem, from its seeds (`decidedSeeds`). -/
def domainOffendersFrom (env : Environment) (n : Name) (links seeds : Array (Name × Name)) :
    Array (Name × String × List Name) :=
  (walkMarked env n links seeds
    (fun c => if domainConsts.contains c then some (.forbid "materialises or counts a domain")
      else none)
    (fun c => !isLibrary env c)).filterMap fun
      | (c, .forbid why, chain) => some (c, why, chain)
      | _ => none

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

/-- The allowances' rendering: each offence with the allowance it falls under. -/
private def renderAllowed (env : Environment) (offs : Array (Offence × Name))
    (reason : Name → String) : MessageData := Id.run do
  let mut m := m!""
  for ((c, why, chain), a) in offs do
    let origin := (moduleOf env c).map toString |>.getD "this file"
    m := m ++ m!"\n• {.ofConstName c} [{origin}]: {why}\n    via {chain}\n    \
      allowed by {.ofConstName a}: \"{reason a}\""
  return m

/-- "walked from …": the propositions a theorem's proof decides, one per
line. -/
private def walkedFrom (props : Array Expr) : MessageData := Id.run do
  let mut m := m!"walked from what its proof decides by evaluation:"
  for p in props do
    m := m ++ (if p.hasLooseBVars then indentD m!"(a proposition under binders)" else indentExpr p)
  return m

/-- The error for a theorem whose proof decides nothing. -/
private def nothingToWalk (rule : String) (n : Name) : MessageData :=
  m!"{rule} cannot check {.ofConstName n}: it is a theorem whose proof decides nothing by \
    evaluation (no `of_decide_eq_true` or sibling applied to a reflexivity proof), so there \
    is no evaluation path to walk"

/-- An allowance: a constant R3 may reach, with the reason. -/
syntax certifyAllowance := ident ppSpace str

/-- R3: `f`'s evaluation path is structural. An error otherwise. On a
theorem, the path of what its proof decides by evaluation. Each
`allow c "reason"` downgrades to a warning what R3 forbids below `c`. -/
syntax (name := certifyStructural) "#certify_structural " ident
  (ppSpace &"allow " sepBy1(certifyAllowance, ", "))? : command

@[command_elab certifyStructural] def elabStructural : CommandElab
  | `(#certify_structural $id $[allow $[$as:certifyAllowance],*]?) => do
    let n ← resolve id
    let mut allows : Array (Ident × Name × String) := #[]
    for a in as.getD #[] do
      match a with
      | `(certifyAllowance| $c:ident $r:str) => allows := allows.push (c, ← resolve c, r.getString)
      | _ => throwUnsupportedSyntax
    let origin ← liftTermElabM do
      match ← checkTerms n with
      | some cs => return Origin.value cs
      | none => match ← theoremOrigin? n with
        | some o => return o
        | none => return .value (evalDeps (← getEnv) n)
    let env ← getEnv
    let cfg ← liftTermElabM Harness.readConfig
    let name := MessageData.ofConstName n
    let (links, seeds, subject, isThm) :
        Array (Name × Name) × Array (Name × Name) × MessageData × Bool := match origin with
      | .value cs => (#[], cs.map (·, n), m!"the evaluation path of {name} ", false)
      | .decided props links seeds =>
        (links, seeds, m!"the evaluation path of {name}, " ++ walkedFrom props ++ m!"\n", true)
      | .nothing => (#[], #[], m!"", true)
    if let .nothing := origin then
      logErrorAt id (nothingToWalk "R3" n); return
    let allowNames : List Name := allows.toList.map fun (_, a, _) => a
    let rep := structuralReport env cfg.route n links seeds allowNames
    let reason (a : Name) : String :=
      match allows.find? (fun (_, b, _) => b == a) with
      | some (_, _, r) => r
      | none => ""
    if rep.errors.isEmpty then
      if rep.allowed.isEmpty then
        logInfo m!"R3 passes: {subject}is structural"
    else
      let msg := m!"R3 fails: {subject}reaches {rep.errors.size} constant(s) R3 forbids:\
        {render env rep.errors}"
      if !isThm || decidedOffenceIsError then logErrorAt id msg else logWarningAt id msg
    unless rep.allowed.isEmpty do
      logWarningAt id m!"R3 allows by name: the evaluation path of {.ofConstName n} reaches \
        {rep.allowed.size} constant(s) R3 forbids through allowed constants; the kernel \
        recomputes them at every check:{renderAllowed env rep.allowed reason}"
    for (c, a, r) in allows do
      if rep.unreached.contains a then
        logErrorAt c m!"R3: the allowance {.ofConstName a} (\"{r}\") names nothing on the \
          evaluation path of {.ofConstName n}"
      else if rep.idle.contains a then
        logErrorAt c m!"R3: the allowance {.ofConstName a} (\"{r}\") is on the evaluation path \
          of {.ofConstName n}, but R3 forbids nothing beneath it"
    unless rep.notes.isEmpty do
      logInfo m!"R3 note: the evaluation path of {.ofConstName n} reaches {rep.notes.size} \
        @[implemented_by] constant(s); under route := kernel the kernel reduces their \
        reference definitions, so this is not an error:{render env rep.notes}"
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
    let subject := m!"the evaluation path of {.ofConstName n} "
    let (offs, subject, walked) ← match ← liftTermElabM (theoremOrigin? n) with
      | some .nothing => logErrorAt id (nothingToWalk "R1" n); return
      | some (.decided props links seeds) =>
        pure (domainOffendersFrom env n links seeds,
          m!"the evaluation path of {.ofConstName n}, " ++ walkedFrom props ++ m!"\n",
          m!", " ++ walkedFrom props)
      | _ => pure (domainOffenders env n, subject, m!"")
    if offs.isEmpty then
      logInfo m!"R1: nothing to report on {.ofConstName n}{walked}"
    else
      logWarningAt id m!"R1 reports: {subject}counts or builds a domain at run time \
        ({offs.size} site(s)); pass a cheap bound instead:{render env offs}"
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
    let (axs, all) ← liftTermElabM <| pinnedAxioms n
    match axiomFailure n m!"{.ofConstName n}" axs all allowed with
    | none => logInfo m!"R4 passes: {.ofConstName n} depends on {axs.toList} ⊆ {allowed}"
    | some msg =>
      let excess := axs.filter fun a => a == ``sorryAx || !allowed.contains a
      logErrorAt id (msg ++ (← liftTermElabM <| producerHint n excess))
  | _ => throwUnsupportedSyntax

/-! ### R4, automatic: the certifier linter -/

/-- Is `ty` (under its leading `∀`s, syntactically) a `Certifier` or an
`Engine`? Type abbreviations are not unfolded. -/
def isCertifierType (ty : Expr) : Bool :=
  match ty.getForallBody.getAppFn.constName? with
  | some n => n == ``Certify.Certifier || n == ``Certify.Engine
  | none => false

/-- Certifier declarations already checked in this process. -/
initialize checkedCertifiers : IO.Ref NameSet ← IO.mkRef {}

/-- R4 on every new `Certifier` or `Engine` of the current module, after
each command. Approved by Matthew for v0.1.3 (2026-10-09). -/
def certifierAxiomLinter : Linter where
  name := `Certify.Lint.certifierAxiomLinter
  run _ := do
    let env ← getEnv
    let seen ← checkedCertifiers.get
    let fresh := env.constants.map₂.foldl (init := #[]) fun acc n ci =>
      if !seen.contains n && !n.isInternal && isCertifierType ci.type then acc.push n else acc
    if fresh.isEmpty then return
    checkedCertifiers.set (fresh.foldl (·.insert ·) seen)
    let cfg ← liftTermElabM Harness.readConfig
    for n in fresh do
      let extra := (cfg.axiomExceptions.find? (·.1 == n)).map (·.2) |>.getD []
      let allowed := cfg.axioms ++ extra
      let (pinned, all) ← liftTermElabM <| pinnedAxioms n
      if let some msg := axiomFailure n m!"the certifier {.ofConstName n}" pinned all allowed
          m!" (Harness.config)" then
        logError msg

initialize addLinter certifierAxiomLinter

end Certify.Lint
