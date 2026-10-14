import LeanCertify

/-! R3 on theorems (v0.2.1, `docs/v0.2.1-statements.md`). A theorem is
walked from what its proof decides by evaluation (`of_decide_eq_true` and
its siblings applied to a reflexivity proof, in the proof or in an auxiliary
theorem generated for it). A theorem whose proof decides nothing is an
error, never a vacuous pass. Each test watched failing against v0.2.0. -/

open Certify

/-! (1) A decided theorem whose decision procedure reaches well-founded
recursion. `halvings` decreases a `Nat` measure, so it compiles to
`WellFounded.Nat.fix`, which the kernel can reduce: `decide +kernel`
accepts the theorem and recomputes the termination argument at every
check. -/

def halvings (n : Nat) : Nat := if h : n < 2 then 0 else 1 + halvings (n / 2)
termination_by n
decreasing_by omega

theorem halvings_8 : halvings 8 = 3 := by decide +kernel

/--
error: R3 fails: the evaluation path of halvings_8, walked from what its proof decides by evaluation:
  halvings 8 = 3
reaches 1 constant(s) R3 forbids:
• WellFounded.Nat.fix [Init.WF]: well-founded recursion on a `Nat` measure: it reduces in the kernel (fuel `measure + 1`), but it is not structural
    via [halvings_8, halvings, WellFounded.Nat.fix]
-/
#guard_msgs in
#certify_structural halvings_8

/-! (2) The same through core. Lean v4.31.0 has no `Nat.sqrt` in core;
`Array.contains` reaches `Array.anyM`, whose `@[implemented_by]` is a note
under the kernel route, and whose reference definition, which the kernel
reduces, loops by `WellFounded.Nat.fix`. -/

theorem has_two : #[1, 2, 3].contains 2 = true := by decide +kernel

/--
error: R3 fails: the evaluation path of has_two, walked from what its proof decides by evaluation:
  #[1, 2, 3].contains 2 = true
reaches 1 constant(s) R3 forbids:
• WellFounded.Nat.fix [Init.WF]: well-founded recursion on a `Nat` measure: it reduces in the kernel (fuel `measure + 1`), but it is not structural
    via [has_two, Array.contains, Array.any, Array.anyM, Array.anyM.loop, WellFounded.Nat.fix]
---
info: R3 note: the evaluation path of has_two reaches 1 @[implemented_by] constant(s); under route := kernel the kernel reduces their reference definitions, so this is not an error:
• Array.anyM [Init.Data.Array.Basic]: @[implemented_by]: the compiled code is not the definition
    via [has_two, Array.contains, Array.any, Array.anyM]
-/
#guard_msgs in
#certify_structural has_two

-- The same on a definition: v0.2.0 stopped at the note and passed it.
def checkHas (xs : Array Nat) : Bool := xs.contains 2

/--
error: R3 fails: the evaluation path of checkHas reaches 1 constant(s) R3 forbids:
• WellFounded.Nat.fix [Init.WF]: well-founded recursion on a `Nat` measure: it reduces in the kernel (fuel `measure + 1`), but it is not structural
    via [checkHas, Array.contains, Array.any, Array.anyM, Array.anyM.loop, WellFounded.Nat.fix]
---
info: R3 note: the evaluation path of checkHas reaches 1 @[implemented_by] constant(s); under route := kernel the kernel reduces their reference definitions, so this is not an error:
• Array.anyM [Init.Data.Array.Basic]: @[implemented_by]: the compiled code is not the definition
    via [checkHas, Array.contains, Array.any, Array.anyM]
-/
#guard_msgs in
#certify_structural checkHas

/-! (3) Structural recursion only: R3 passes, and says what it walked.
Plain `decide` leaves `of_decide_eq_true` in the proof; `decide +kernel`
leaves it in an auxiliary theorem. -/

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

theorem sum_4 : sumTo 4 = 10 := by decide
theorem sum_5 : sumTo 5 = 15 ∧ sumTo 1 = 1 := by decide +kernel

/--
info: R3 passes: the evaluation path of sum_4, walked from what its proof decides by evaluation:
  sumTo 4 = 10
is structural
-/
#guard_msgs in
#certify_structural sum_4

/--
info: R3 passes: the evaluation path of sum_5, walked from what its proof decides by evaluation:
  sumTo 5 = 15 ∧ sumTo 1 = 1
is structural
-/
#guard_msgs in
#certify_structural sum_5

/--
info: R1: nothing to report on sum_4, walked from what its proof decides by evaluation:
  sumTo 4 = 10
-/
#guard_msgs in
#certify_domain sum_4

/-! A fact proved by a certifier's gate is walked through the certifier's
check functions only, not its untrusted producer (here `partial`, which
R3 would reject). -/

def squares : Certifier Nat Nat (fun s => ∃ k, k * k = s) where
  check s c := decide (c * c = s)
  sound _ c h := ⟨c, of_decide_eq_true h⟩

partial def rootFrom (s k : Nat) : Option Nat :=
  if k * k == s then some k else if k > s then none else rootFrom s (k + 1)

def squaresEngine : Engine Nat Nat Empty (fun s => ∃ k, k * k = s) where
  yes := squares
  no := .empty
  produce s _ := match rootFrom s 0 with
    | some k => .pass k
    | none => .flag

theorem sq_64 : ∃ k, k * k = 64 := squaresEngine.yes.verdict 64 8

/--
info: R3 passes: the evaluation path of sq_64, walked from what its proof decides by evaluation:
  squaresEngine.yes.check 64 8 = true
is structural
-/
#guard_msgs in
#certify_structural sq_64

/-! (4) No decided content: an error, never a vacuous pass. A hypothesis
`h : decide p = true` is not evaluated by the kernel, so a proof that
applies `of_decide_eq_true` to it decides nothing either. -/

theorem add_zero' (n : Nat) : n + 0 = n := Nat.add_zero n

theorem root_ok (c s : Nat) (h : decide (c * c = s) = true) : c * c = s :=
  of_decide_eq_true h

/--
error: R3 cannot check add_zero': it is a theorem whose proof decides nothing by evaluation (no `of_decide_eq_true` or sibling applied to a reflexivity proof), so there is no evaluation path to walk
-/
#guard_msgs in
#certify_structural add_zero'

/--
error: R3 cannot check root_ok: it is a theorem whose proof decides nothing by evaluation (no `of_decide_eq_true` or sibling applied to a reflexivity proof), so there is no evaluation path to walk
-/
#guard_msgs in
#certify_structural root_ok

/--
error: R1 cannot check add_zero': it is a theorem whose proof decides nothing by evaluation (no `of_decide_eq_true` or sibling applied to a reflexivity proof), so there is no evaluation path to walk
-/
#guard_msgs in
#certify_domain add_zero'

/-! (5) An allowance names a reached constant and a reason, and downgrades
to a warning exactly what R3 forbids beneath that constant. -/

def steps (n : Nat) : Nat := if h : n = 0 then 0 else 1 + steps (n - 1)
termination_by n
decreasing_by omega

theorem both : halvings 8 = 3 ∧ steps 2 = 2 := by decide +kernel

/--
error: R3 fails: the evaluation path of both, walked from what its proof decides by evaluation:
  halvings 8 = 3 ∧ steps 2 = 2
reaches 1 constant(s) R3 forbids:
• WellFounded.Nat.fix [Init.WF]: well-founded recursion on a `Nat` measure: it reduces in the kernel (fuel `measure + 1`), but it is not structural
    via [both, steps, WellFounded.Nat.fix]
---
warning: R3 allows by name: the evaluation path of both reaches 1 constant(s) R3 forbids through allowed constants; the kernel recomputes them at every check:
• WellFounded.Nat.fix [Init.WF]: well-founded recursion on a `Nat` measure: it reduces in the kernel (fuel `measure + 1`), but it is not structural
    via [both, halvings, WellFounded.Nat.fix]
    allowed by halvings: "three halvings of a literal"
-/
#guard_msgs in
#certify_structural both allow halvings "three halvings of a literal"

-- Everything forbidden lies under an allowance: a warning only.
/--
warning: R3 allows by name: the evaluation path of halvings_8 reaches 1 constant(s) R3 forbids through allowed constants; the kernel recomputes them at every check:
• WellFounded.Nat.fix [Init.WF]: well-founded recursion on a `Nat` measure: it reduces in the kernel (fuel `measure + 1`), but it is not structural
    via [halvings_8, halvings, WellFounded.Nat.fix]
    allowed by halvings: "three halvings of a literal"
-/
#guard_msgs in
#certify_structural halvings_8 allow halvings "three halvings of a literal"

-- An allowance that names nothing on the path is an error, and so is one
-- that is reached but has nothing forbidden beneath it.
/--
error: R3 fails: the evaluation path of halvings_8, walked from what its proof decides by evaluation:
  halvings 8 = 3
reaches 1 constant(s) R3 forbids:
• WellFounded.Nat.fix [Init.WF]: well-founded recursion on a `Nat` measure: it reduces in the kernel (fuel `measure + 1`), but it is not structural
    via [halvings_8, halvings, WellFounded.Nat.fix]
---
error: R3: the allowance sumTo ("mistyped") names nothing on the evaluation path of halvings_8
-/
#guard_msgs in
#certify_structural halvings_8 allow sumTo "mistyped"

/--
info: R3 passes: the evaluation path of sum_4, walked from what its proof decides by evaluation:
  sumTo 4 = 10
is structural
---
error: R3: the allowance sumTo ("not needed") is on the evaluation path of sum_4, but R3 forbids nothing beneath it
-/
#guard_msgs in
#certify_structural sum_4 allow sumTo "not needed"

-- Allowances work the same on a definition.
def checkHalvings (n : Nat) : Bool := halvings n == 3

/--
warning: R3 allows by name: the evaluation path of checkHalvings reaches 1 constant(s) R3 forbids through allowed constants; the kernel recomputes them at every check:
• WellFounded.Nat.fix [Init.WF]: well-founded recursion on a `Nat` measure: it reduces in the kernel (fuel `measure + 1`), but it is not structural
    via [checkHalvings, halvings, WellFounded.Nat.fix]
    allowed by halvings: "small inputs only"
-/
#guard_msgs in
#certify_structural checkHalvings allow halvings "small inputs only"
