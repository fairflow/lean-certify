import LeanCertify

/-! Deciders (v0.3): the race, the fallback, the budget raise, and the gate
rejecting a lying tool (R9), each watched and pinned by `#guard_msgs`.

The toy property: a natural number is even. -/

open Certify

def Even' (n : Nat) : Prop := n % 2 = 0

/-- Evenness, certified by a half. -/
def evenK : Certifier Nat Nat Even' where
  check n k := decide (2 * k = n)
  sound n k h := by have := of_decide_eq_true h; unfold Even'; omega

/-- Oddness, certified by a half. -/
def oddK : Certifier Nat Nat (fun n => Even' n → False) where
  check n k := decide (2 * k + 1 = n)
  sound n k h he := by have := of_decide_eq_true h; unfold Even' at he; omega

/-- A prover that needs a budget of at least `n`. -/
def slowProver : Prover Nat Even' :=
  { name := "slow", Cert := Nat, certifier := evenK,
    produce := fun n b => if n ≤ b ∧ n % 2 = 0 then some (n / 2) else none }

/-- A disprover that answers at once, correctly. -/
def fastDisprover : Disprover Nat Even' :=
  { name := "fast", RCert := Nat, certifier := oddK,
    produce := fun n _ => if n % 2 = 1 then some (n / 2) else none }

/-- A disprover that always answers, wrongly: the gate must reject it. -/
def liar : Disprover Nat Even' :=
  { name := "liar", RCert := Nat, certifier := oddK, produce := fun _ _ => some 0 }

def showD {s : Nat} : Decision Even' s → String
  | .yes _ t => s!"yes by {t}"
  | .no _ t => s!"no by {t}"
  | .flag r => s!"flag: {r}"

/-- The liar is rejected, the slow prover needs the raised budget (8 → 32),
and the fallback pair decides an odd number. -/
def D : Decider Nat Even' :=
  { prover := slowProver, disprover := liar, fallback := [(slowProver, fastDisprover)] }

def cfg : RunConfig := { mode := .sequential, budget := 8, flagReruns := 1, budgetFactor := 4 }

/-- info: yes by slow -/
#guard_msgs in #eval do IO.println (showD (← D.run cfg 6))

/-- info: yes by slow -/
#guard_msgs in #eval do IO.println (showD (← D.run cfg 20))

/-- info: no by fast -/
#guard_msgs in #eval do IO.println (showD (← D.run cfg 7))

/--
info: flag: budget 8: slow: no certificate within the budget; budget 8: liar: certificate REJECTED by its certifier (a tool defect); budget 32: slow: no certificate within the budget; budget 32: liar: certificate REJECTED by its certifier (a tool defect); budget 8: slow: no certificate within the budget; budget 8: fast: no certificate within the budget; budget 32: slow: no certificate within the budget; budget 32: fast: no certificate within the budget
-/
#guard_msgs in #eval do IO.println (showD (← D.run cfg 100))

/-- The race mode decides the same cases. -/
def cfgRace : RunConfig := { cfg with mode := .race }

/-- info: no by fast -/
#guard_msgs in #eval do IO.println (showD (← D.run cfgRace 7))

/-! ## The settings file pattern (B.1) -/

def Harness.tools : Harness.Registry Nat Even' :=
  [ .prover "slow" slowProver, .disprover "fast" fastDisprover, .disprover "liar" liar ]

def Harness.decider : Harness.DeciderConfig where
  prover    := "slow"
  disprover := "liar"
  fallback  := [("slow", "fast")]
  run       := { mode := .sequential, budget := 8 }

/-- info: decider ok: prover slow, disprover liar, 1 fallback pair(s) -/
#guard_msgs in #certify_decider Harness.decider

/-- error: #certify_decider: unknown fallback disprover 'fats' -/
#guard_msgs in #certify_decider { Harness.decider with fallback := [("slow", "fats")] }

/--
info: {"run":
 {"mode": "sequential",
  "flagReruns": 2,
  "deadlineSec": 600,
  "budgetFactor": 4,
  "budget": 8},
 "prover": "slow",
 "fallback": [["slow", "fast"]],
 "disprover": "liar"}
-/
#guard_msgs in #eval IO.println (Lean.toJson Harness.decider).pretty
