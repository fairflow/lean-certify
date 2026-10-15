/-
# Deciders: a prover, a disprover, and fallback pairs (v0.3)

`docs/v0.3-statements.md` (approved by Matthew, 2026-10-15, configuration
option 1).  An `Engine` (v0.1) bundles one producer with both certifiers; a
decider separates the two directions, so that the fastest tool on each side
can be used, and adds fallback pairs tried in order.  To fall back on one
side only, repeat the other side's tool in the pair.

Every answer is gated by its certifier: a produced certificate is checked by
the certifier's compiled `check`, and `Decision.yes` carries the proposition
obtained from `sound`.  The kernel-checked fact still goes through
`Certifier.verdict` (step 6), unchanged.  Nothing here is about
completeness: a decider never claims more than its certificates.
-/
import LeanCertify.Certifier
import LeanCertify.Config

open Lean

namespace Certify

/-- A prover: an untrusted producer of certificates for `Holds`, and the
certifier that judges them.  `none` means "not found within the budget". -/
structure Prover (Spec : Type) (Holds : Spec → Prop) where
  name : String
  Cert : Type
  certifier : Certifier Spec Cert Holds
  produce : Spec → Nat → Option Cert

/-- A disprover: the same for `Holds s → False`. -/
structure Disprover (Spec : Type) (Holds : Spec → Prop) where
  name : String
  RCert : Type
  certifier : Certifier Spec RCert (fun s => Holds s → False)
  produce : Spec → Nat → Option RCert

/-- A decider: a prover and a disprover, then fallback pairs in order. -/
structure Decider (Spec : Type) (Holds : Spec → Prop) where
  prover : Prover Spec Holds
  disprover : Disprover Spec Holds
  fallback : List (Prover Spec Holds × Disprover Spec Holds) := []

/-- A decided case, with the evidence and the tool that found it. -/
inductive Decision {Spec : Type} (Holds : Spec → Prop) (s : Spec) where
  | yes (h : Holds s) (tool : String)
  | no (h : Holds s → False) (tool : String)
  /-- Every pair exhausted its budgets (R5); the report lists every attempt. -/
  | flag (report : String)

variable {Spec Cert RCert : Type} {Holds : Spec → Prop}

/-- A `yes` decision carries `Holds s`. -/
theorem Decision.sound_yes {s : Spec} {d : Decision Holds s} {h : Holds s} {t : String}
    (_ : d = .yes h t) : Holds s := h

/-- A `no` decision carries `Holds s → False`. -/
theorem Decision.sound_no {s : Spec} {d : Decision Holds s} {h : Holds s → False}
    {t : String} (_ : d = .no h t) : Holds s → False := h

/-- The prover side of an engine. -/
def Prover.ofEngine (E : Engine Spec Cert RCert Holds) (name : String) : Prover Spec Holds where
  name := name
  Cert := Cert
  certifier := E.yes
  produce s n := match E.produce s n with
    | .pass c => some c
    | _ => none

/-- The disprover side of an engine. -/
def Disprover.ofEngine (E : Engine Spec Cert RCert Holds) (name : String) :
    Disprover Spec Holds where
  name := name
  RCert := RCert
  certifier := E.no
  produce s n := match E.produce s n with
    | .fail r => some r
    | _ => none

/-- Within a pair: race the prover and the disprover in two threads, or run
one after the other. -/
inductive Mode | race | sequential
  deriving Repr, DecidableEq, ToJson, FromJson

/-- Run-time settings of a decider. -/
structure RunConfig where
  mode : Mode := .race
  /-- Handed to `produce`; raised on a flag (R5). -/
  budget : Nat := 1000
  /-- R5: how many times a pair's budget is raised before the next pair. -/
  flagReruns : Nat := 2
  /-- R5: the multiplier per raise. -/
  budgetFactor : Nat := 4
  /-- R7: wall-clock deadline for the whole run. -/
  deadlineSec : Nat := 600
  deriving Repr, ToJson, FromJson

/-- Gate a prover's certificate: a decision, nothing found, or a report line. -/
def Prover.gate (p : Prover Spec Holds) (s : Spec) : Option p.Cert →
    Option (Decision Holds s) ⊕ String
  | none => .inr s!"{p.name}: no certificate within the budget"
  | some c =>
    if h : p.certifier.check s c = true then .inl (some (.yes (p.certifier.sound s c h) p.name))
    else .inr s!"{p.name}: certificate REJECTED by its certifier (a tool defect)"

/-- Gate a disprover's certificate. -/
def Disprover.gate (d : Disprover Spec Holds) (s : Spec) : Option d.RCert →
    Option (Decision Holds s) ⊕ String
  | none => .inr s!"{d.name}: no certificate within the budget"
  | some r =>
    if h : d.certifier.check s r = true then .inl (some (.no (d.certifier.sound s r h) d.name))
    else .inr s!"{d.name}: certificate REJECTED by its certifier (a tool defect)"

/-- One attempt with one pair at one budget: the decision if a certificate
passed its certifier, and the report lines. -/
def tryPair (p : Prover Spec Holds) (d : Disprover Spec Holds) (s : Spec) (budget : Nat)
    (mode : Mode) (deadline : Nat) : IO (Option (Decision Holds s) × List String) := do
  match mode with
  | .sequential =>
    match p.gate s (p.produce s budget) with
    | .inl (some dec) => return (some dec, [])
    | .inl none => return (none, [])
    | .inr r₁ =>
      match d.gate s (d.produce s budget) with
      | .inl (some dec) => return (some dec, [r₁])
      | .inl none => return (none, [r₁])
      | .inr r₂ => return (none, [r₁, r₂])
  | .race =>
    let tp := Task.spawn (prio := .dedicated) fun _ => p.gate s (p.produce s budget)
    let td := Task.spawn (prio := .dedicated) fun _ => d.gate s (d.produce s budget)
    let mut reports : List String := []
    let mut pDone := false
    let mut dDone := false
    while !(pDone && dDone) do
      if (← IO.monoMsNow) ≥ deadline then
        return (none, reports ++ ["deadline reached inside the pair"])
      if !pDone && (← IO.hasFinished tp) then
        pDone := true
        match tp.get with
        | .inl (some dec) => return (some dec, reports)
        | .inl none => pure ()
        | .inr r => reports := reports ++ [r]
      if !dDone && (← IO.hasFinished td) then
        dDone := true
        match td.get with
        | .inl (some dec) => return (some dec, reports)
        | .inl none => pure ()
        | .inr r => reports := reports ++ [r]
      IO.sleep 1
    return (none, reports)

/-- **Run a decider**: the pairs in order, each at budgets raised `flagReruns`
times by `budgetFactor`; the first certified answer decides.  Every attempt
is in the report of a `flag`. -/
def Decider.run (D : Decider Spec Holds) (cfg : RunConfig) (s : Spec) :
    IO (Decision Holds s) := do
  let deadline := (← IO.monoMsNow) + cfg.deadlineSec * 1000
  let mut report : List String := []
  for (p, d) in (D.prover, D.disprover) :: D.fallback do
    let mut budget := cfg.budget
    for _ in [0:cfg.flagReruns + 1] do
      if (← IO.monoMsNow) ≥ deadline then
        return .flag (String.intercalate "; " (report ++ ["deadline reached"]))
      let (dec?, rs) ← tryPair p d s budget cfg.mode deadline
      if let some dec := dec? then return dec
      report := report ++ rs.map (s!"budget {budget}: " ++ ·)
      budget := budget * cfg.budgetFactor
  return .flag (String.intercalate "; " report)

end Certify

namespace Harness

open Certify

/-- The decider of a project, by tool names (`docs/v0.3-statements.md` B.1).
Lives in the project's settings file; JSON is generated from it. -/
structure DeciderConfig where
  prover : String
  disprover : String
  fallback : List (String × String) := []
  run : RunConfig := {}
  deriving Repr, ToJson, FromJson

/-- A tool a project offers, by name. -/
inductive Tool (Spec : Type) (Holds : Spec → Prop) where
  | pair (name : String) (p : Prover Spec Holds) (d : Disprover Spec Holds)
  | prover (name : String) (p : Prover Spec Holds)
  | disprover (name : String) (d : Disprover Spec Holds)

/-- The tools of a project. -/
abbrev Registry (Spec : Type) (Holds : Spec → Prop) := List (Tool Spec Holds)

variable {Spec : Type} {Holds : Spec → Prop}

def Registry.prover? (R : Registry Spec Holds) (n : String) : Option (Prover Spec Holds) :=
  R.findSome? fun
    | .pair m p _ => if m == n then some p else none
    | .prover m p => if m == n then some p else none
    | .disprover _ _ => none

def Registry.disprover? (R : Registry Spec Holds) (n : String) :
    Option (Disprover Spec Holds) :=
  R.findSome? fun
    | .pair m _ d => if m == n then some d else none
    | .disprover m d => if m == n then some d else none
    | .prover _ _ => none

/-- The decider a configuration names, or the first name not in the registry. -/
def Registry.decider (R : Registry Spec Holds) (c : DeciderConfig) :
    Except String (Decider Spec Holds) := do
  let p ← match R.prover? c.prover with
    | some p => pure p
    | none => throw s!"unknown prover '{c.prover}'"
  let d ← match R.disprover? c.disprover with
    | some d => pure d
    | none => throw s!"unknown disprover '{c.disprover}'"
  let fb ← c.fallback.mapM fun (pn, dn) => do
    let p' ← match R.prover? pn with
      | some p' => pure p'
      | none => throw s!"unknown fallback prover '{pn}'"
    let d' ← match R.disprover? dn with
      | some d' => pure d'
      | none => throw s!"unknown fallback disprover '{dn}'"
    pure (p', d')
  pure { prover := p, disprover := d, fallback := fb }

/-- Check a configuration's names against the registry (for `#certify_decider`). -/
def Registry.validate (R : Registry Spec Holds) (c : DeciderConfig) : IO Unit :=
  match R.decider c with
  | .ok _ => IO.println s!"decider ok: prover {c.prover}, disprover {c.disprover}, \
{c.fallback.length} fallback pair(s)"
  | .error e => throw (IO.userError s!"#certify_decider: {e}")

end Harness

/-- `#certify_decider D` checks every tool name in the decider configuration
`D` against the project's `Harness.tools`, when the settings file is
compiled; an unknown name is an error. -/
macro "#certify_decider " d:term : command => do
  let tools := mkIdent `Harness.tools
  `(command| #eval Harness.Registry.validate $tools $d)

namespace Certify.Cli

open Harness

/-- Command-line overrides of the run settings, for one run. -/
def applyFlags (cfg : RunConfig) : List String → Except String (RunConfig × List String)
  | [] => pure (cfg, [])
  | a :: rest =>
    if a.startsWith "--deadline=" then
      match (a.drop 11).toString.toNat? with
      | some n => applyFlags { cfg with deadlineSec := n } rest
      | none => throw s!"bad {a}"
    else if a.startsWith "--budget=" then
      match (a.drop 9).toString.toNat? with
      | some n => applyFlags { cfg with budget := n } rest
      | none => throw s!"bad {a}"
    else if a == "--mode=race" then applyFlags { cfg with mode := .race } rest
    else if a == "--mode=sequential" then applyFlags { cfg with mode := .sequential } rest
    else do
      let (c, r) ← applyFlags cfg rest
      pure (c, a :: r)

/-- **The generic decider executable.**  A project's `main` is
`Certify.Cli.main Harness.tools parse Harness.decider`.  Exit codes: 0 yes,
1 no, 2 usage or parse error, 3 flag.  `--json` prints the decider
configuration as JSON and exits. -/
def main {Spec : Type} {Holds : Spec → Prop} (R : Registry Spec Holds)
    (parse : String → Except String Spec) (c : DeciderConfig) (args : List String) :
    IO UInt32 := do
  if args.contains "--json" then
    IO.println (toJson c).pretty
    return 0
  match applyFlags c.run args with
  | .error e => IO.println s!"error: {e}"; return 2
  | .ok (run, rest) =>
    match rest with
    | [src] =>
      match parse src, R.decider c with
      | .error e, _ => IO.println s!"parse error: {e}"; return 2
      | _, .error e => IO.println s!"configuration error: {e}"; return 2
      | .ok s, .ok D =>
        match ← D.run run s with
        | .yes _ t => IO.println s!"YES  (certified by {t})"; return 0
        | .no _ t => IO.println s!"NO   (certified by {t})"; return 1
        | .flag r => IO.println s!"FLAG {r}"; return 3
    | _ => IO.println "usage: <tool> [--deadline=N] [--budget=N] [--mode=race|sequential] \
[--json] \"<specification>\""; return 2

end Certify.Cli
