import LeanCertify

/-! `partial_fixpoint`, axioms on the evaluation path, and the producer
outside the pin (2026-10-21).

* R3 reports truthfully that the kernel does not reduce a `partial_fixpoint`
  definition, and says where such a definition belongs: in `produce`, or in
  `Holds` with a certificate checked against it. It is not an error to use
  one; it is an error to make the kernel evaluate one.
* R3 counts an axiom that is not a proposition (`Classical.choice`,
  `sorryAx`) as stuck, like an opaque constant. Proofs are not walked, so a
  classical soundness proof stays out of R3.
* R4 pins what a result depends on, not the producer: an `Engine`'s
  `produce` may reach `Classical.choice`. A `sorry` fails everywhere.
-/

open Certify

/-! ### R3 on `partial_fixpoint` (found in lax-logic's research, 2026-10-20) -/

/-- The Collatz iteration, counting steps: nobody knows that it terminates. -/
def collatz (n k : Nat) : Option Nat :=
  if n ≤ 1 then some k
  else if n % 2 = 0 then collatz (n / 2) (k + 1) else collatz (3 * n + 1) (k + 1)
partial_fixpoint

/--
error: R3 fails: the evaluation path of collatz reaches 1 constant(s) R3 forbids:
• Lean.Order.fix [Init.Internal.Order.Basic]: partial_fixpoint (a least fixpoint): not kernel-reducible; use it in `produce`, or state facts about it in `Holds` and check them with a certificate
    via [collatz, Lean.Order.fix]
-/
#guard_msgs in
#certify_structural collatz

/-! ### R3 on axioms in the code -/

/-- A checker that decides by `Classical.propDecidable` (what `open Classical`
gives): the kernel is stuck at `Classical.choice`. -/
noncomputable def checkClassical (n : Nat) : Bool := @decide (n = n) (Classical.propDecidable _)

/--
error: R3 fails: the evaluation path of checkClassical reaches 1 constant(s) R3 forbids:
• Classical.choice [Init.Prelude]: an axiom that is not a proposition: no value to reduce
    via [checkClassical, Classical.propDecidable, Classical.choice]
-/
#guard_msgs in
#certify_structural checkClassical

/-- warning: declaration uses `sorry` -/
#guard_msgs in
def checkSorry (n : Nat) : Bool := n == sorry

/--
error: R3 fails: the evaluation path of checkSorry reaches 1 constant(s) R3 forbids:
• sorryAx [Init.Prelude]: a `sorry`: no value to reduce
    via [checkSorry, sorryAx]
---
info: R3 note: the evaluation path of checkSorry reaches 3 @[implemented_by] constant(s); under route := kernel the kernel reduces their reference definitions, so this is not an error:
• Lean.Name.num [Init.Prelude]: @[implemented_by]: the compiled code is not the definition
    via [checkSorry, Lean.Name.num]
• Lean.Name.str [Init.Prelude]: @[implemented_by]: the compiled code is not the definition
    via [checkSorry, Lean.Name.str]
• Lean.Name.anonymous [Init.Prelude]: @[implemented_by]: the compiled code is not the definition
    via [checkSorry, Lean.Name.anonymous]
-/
#guard_msgs in
#certify_structural checkSorry

/-! ### Guards: proofs are not walked

A classical *proof* never blocks the kernel: R3 walks the code, not the
proofs, so neither a classical `sound` nor a classical proof inside the code
is reported. -/

theorem le_or_gt' (n : Nat) : n ≤ 5 ∨ 5 < n := by
  rcases Classical.em (n ≤ 5) with h | h
  · exact .inl h
  · exact .inr (Nat.lt_of_not_le h)

/-- info: 'le_or_gt'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms le_or_gt'

/-- The code is structural; a classical proof sits inside it. -/
def checkBelow (n : Nat) : Bool :=
  (⟨n, le_or_gt' n⟩ : {m : Nat // m ≤ 5 ∨ 5 < m}).val == n

/-- info: R3 passes: the evaluation path of checkBelow is structural -/
#guard_msgs in
#certify_structural checkBelow

/--
error: R4 fails: the certifier classicalSound depends on [Classical.choice], outside the allow-list [propext,
 Quot.sound] (Harness.config)
-/
#guard_msgs in
def classicalSound : Certifier Nat Unit (fun n => n ≤ 5 ∨ 5 < n) where
  check _ _ := true
  sound n _ _ := le_or_gt' n

/-- info: R3 passes: the evaluation path of classicalSound is structural -/
#guard_msgs in
#certify_structural classicalSound

/-! ### R4: the pin does not see the producer -/

/-- An unbounded search for a square root, by `partial_fixpoint`. -/
def rootFrom (s k : Nat) : Option Nat :=
  if k * k = s then some k else if s < k * k then none else rootFrom s (k + 1)
partial_fixpoint

def sqYes : Certifier Nat Nat (fun s => ∃ k, k * k = s) where
  check s c := decide (c * c = s)
  sound _ c h := ⟨c, of_decide_eq_true h⟩

#guard_msgs in
/-- The producer reaches `Classical.choice`; the certifiers do not, so R4
passes silently. -/
def sqEngine : Engine Nat Nat Empty (fun s => ∃ k, k * k = s) where
  yes := sqYes
  no := .empty
  produce s _ := match rootFrom s 0 with
    | some k => .pass k
    | none => .flag

/-- info: R4 passes: sqEngine depends on [] ⊆ [propext, Quot.sound] -/
#guard_msgs in
#certify_axioms sqEngine

/-- A result stated with the named certifier depends on no axiom. -/
theorem sq_49 : ∃ k, k * k = 49 := sqYes.verdict 49 7

/-- info: 'sq_49' does not depend on any axioms -/
#guard_msgs in #print axioms sq_49

/-- A result stated through the engine names the engine, and with it the
producer: Lean's axiom count then includes the producer's. State results with
the named certifier. -/
theorem sq_49' : ∃ k, k * k = 49 := sqEngine.yes.verdict 49 7

/-- info: 'sq_49'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sq_49'

/--
error: R4 fails: sq_49' depends on [Classical.choice], outside the allow-list [propext, Quot.sound]
  they enter through the producer of sqEngine: state the result with the named certifier (`K.verdict`, not `E.yes.verdict`), whose term does not mention the producer
-/
#guard_msgs in
#certify_axioms sq_49'

/-- info: R4 passes: sq_49 depends on [] ⊆ [propext, Quot.sound] -/
#guard_msgs in
#certify_axioms sq_49

/-! ### `sorry` fails everywhere, the producer included -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
def sorryRoot (s : Nat) : Option Nat := sorry

/--
error: R4 fails: the producer of sqSorry depends on sorryAx: a `sorry` fails everywhere, the producer included
-/
#guard_msgs in
def sqSorry : Engine Nat Nat Empty (fun s => ∃ k, k * k = s) where
  yes := sqYes
  no := .empty
  produce s _ := match sorryRoot s with
    | some k => .pass k
    | none => .flag
