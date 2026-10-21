import LeanCertify

/-! `sorryAx` fails R4 even when the project's allow-list names it
(Matthew, 2026-10-21: a `sorry` always fails). -/

open Certify

def Harness.config : Harness.Config := { axioms := [``propext, ``Quot.sound, ``sorryAx] }

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem sorried : 2 + 2 = 4 := sorry

/--
error: R4 fails: sorried depends on [sorryAx], outside the allow-list [propext, Quot.sound, sorryAx]; sorryAx is never allowed
-/
#guard_msgs in
#certify_axioms sorried

/--
warning: declaration uses `sorry`
---
error: R4 fails: the certifier sorryCert depends on [sorryAx], outside the allow-list [propext,
 Quot.sound,
 sorryAx] (Harness.config); sorryAx is never allowed
-/
#guard_msgs in
def sorryCert : Certifier Nat Unit (fun n => n = n) where
  check _ _ := true
  sound _ _ _ := sorry
