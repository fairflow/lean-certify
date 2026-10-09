import LeanCertify

/-! The interface and the R2 lint, each watched passing and failing. -/

open Certify

def Harness.config : Harness.Config := { budgetNames := [`hiddenBound] }

/-- Perfect squares, certified by a root. -/
def squares : Certifier Nat Nat (fun s => ∃ k, k * k = s) where
  check s c := decide (c * c = s)
  sound _ c h := ⟨c, of_decide_eq_true h⟩

theorem sq_49 : ∃ k, k * k = 49 := squares.verdict 49 7

/-- info: 'sq_49' does not depend on any axioms -/
#guard_msgs in #print axioms sq_49

/-- info: R4 passes: sq_49 depends on [] ⊆ [propext, Quot.sound] -/
#guard_msgs in
#certify_axioms sq_49
/--
info: R3 passes: the evaluation path of squares is structural
-/
#guard_msgs in
#certify_structural squares
/-- info: R2 passes: the property of squares mentions no budget -/
#guard_msgs in
#certify_statement squares

-- The gate watched failing: a wrong root.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  squares.check 49 6 = true
is false
-/
#guard_msgs in
example : ∃ k, k * k = 49 := squares.verdict 49 6

-- An engine with no refutation side.
def squaresEngine : Engine Nat Nat Empty (fun s => ∃ k, k * k = s) where
  yes := squares
  no := .empty
  produce s := fun budget =>
    match (List.range (budget + 1)).find? (fun k => k * k == s) with
    | some k => .pass k
    | none => .flag

/--
info: R2 passes: the property of squaresEngine mentions no budget
-/
#guard_msgs in
#certify_statement squaresEngine
/--
info: R3 passes: the evaluation path of squaresEngine is structural
-/
#guard_msgs in
#certify_structural squaresEngine

-- R2 watched failing: a fuelled search in the property.
def searchWithin (fuel s : Nat) : Bool := (List.range fuel).any fun k => k * k == s

def fuelled : Certifier Nat Unit (fun s => searchWithin 64 s = true) where
  check s _ := searchWithin 64 s
  sound _ _ h := h

/--
error: R2 fails: the property of fuelled mentions a budget (1 site(s)); a budget belongs in `produce` or `Engine.Complete`:
• searchWithin [this file]: it takes a budget argument `fuel`
    via [Holds, searchWithin]
-/
#guard_msgs in
#certify_statement fuelled

-- Reached through two project definitions whose names do not mention fuel.
def withinSq (s : Nat) : Prop := searchWithin 64 s = true
def provableSq (s : Nat) : Prop := withinSq s

def indirect : Certifier Nat Unit provableSq where
  check s _ := searchWithin 64 s
  sound _ _ h := h

/--
error: R2 fails: the property of indirect mentions a budget (1 site(s)); a budget belongs in `produce` or `Engine.Complete`:
• searchWithin [this file]: it takes a budget argument `fuel`
    via [Holds, provableSq, withinSq, searchWithin]
-/
#guard_msgs in
#certify_statement indirect

-- A budget the name heuristic misses, caught by `Harness.config.budgetNames`.
def hiddenBound : Nat := 64
def bounded : Certifier Nat Unit (fun s => s < hiddenBound) where
  check s _ := decide (s < hiddenBound)
  sound _ _ h := of_decide_eq_true h

/--
error: R2 fails: the property of bounded mentions a budget (1 site(s)); a budget belongs in `produce` or `Engine.Complete`:
• hiddenBound [this file]: listed in Harness.config.budgetNames
    via [Holds, hiddenBound]
-/
#guard_msgs in
#certify_statement bounded

-- R3 on a certifier: only `check` is walked, and a well-founded `check` fails.
def halvings (n : Nat) : Nat := if n < 2 then 0 else 1 + halvings (n / 2)
termination_by n
decreasing_by omega

def wfCert : Certifier Nat Unit (fun _ => True) where
  check n _ := halvings n == 3
  sound _ _ _ := trivial

/--
error: R3 fails: the evaluation path of wfCert reaches 1 constant(s) R3 forbids:
• WellFounded.Nat.fix [Init.WF]: well-founded recursion on a `Nat` measure: it reduces in the kernel (fuel `measure + 1`), but it is not structural
    via [wfCert, halvings, WellFounded.Nat.fix]
-/
#guard_msgs in
#certify_structural wfCert

-- A generic certifier: the lints open its parameters (found on locus's
-- `wbisimCertifier`, 2026-10-09).
def memCert {α : Type} [DecidableEq α] : Certifier (List α × α) Nat (fun s => s.2 ∈ s.1) where
  check s i := s.1[i]? == some s.2
  sound s i h := List.mem_of_getElem? (by simpa using h)

/--
info: R3 passes: the evaluation path of memCert is structural
-/
#guard_msgs in
#certify_structural memCert
/-- info: R2 passes: the property of memCert mentions no budget -/
#guard_msgs in
#certify_statement memCert

def fuelledGeneric {α : Type} : Certifier (List α) Unit (fun l => searchWithin 64 l.length = true) where
  check l _ := searchWithin 64 l.length
  sound _ _ h := h

/--
error: R2 fails: the property of fuelledGeneric mentions a budget (1 site(s)); a budget belongs in `produce` or `Engine.Complete`:
• searchWithin [this file]: it takes a budget argument `fuel`
    via [Holds, searchWithin]
-/
#guard_msgs in
#certify_statement fuelledGeneric

/-! R4 runs by itself on every certifier (v0.1.3): a `sound` proof that
pulls in `Classical.choice` fails at its declaration. -/

/--
error: R4 fails: the certifier choiceCert depends on [Classical.choice], outside the allow-list [propext,
 Quot.sound] (Harness.config)
-/
#guard_msgs in
def choiceCert : Certifier Nat Unit (fun n => n = n ∨ n ≠ n) where
  check _ _ := true
  sound n _ _ := Classical.em (n = n)

-- The clean certifiers above passed silently.
