import LeanCertify

/-! Each lint watched passing and failing. -/

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

def checkS (n s : Nat) : Bool := (List.range (n + 1)).foldl (· + ·) 0 == s && sumTo n == s

/-- info: R3 passes: the evaluation path of checkS is structural -/
#guard_msgs in
#certify_structural checkS

def wfLog (n : Nat) : Nat := if h : n < 2 then 0 else 1 + wfLog (n / 2)
termination_by n
decreasing_by omega

def checkWF (n : Nat) : Bool := wfLog n == 3

/--
error: R3 fails: the evaluation path of checkWF reaches 1 constant(s) R3 forbids:
• WellFounded.Nat.fix [Init.WF]: well-founded recursion on a `Nat` measure: it reduces in the kernel (fuel `measure + 1`), but it is not structural
    via [checkWF, wfLog, WellFounded.Nat.fix]
-/
#guard_msgs in
#certify_structural checkWF

partial def loop (n : Nat) : Nat := if n == 0 then 0 else loop (n - 1)
def checkPartial (n : Nat) : Bool := loop n == 0

/--
error: R3 fails: the evaluation path of checkPartial reaches 1 constant(s) R3 forbids:
• loop [this file]: opaque (a `partial def` or `opaque`): no value to reduce
    via [checkPartial, loop]
-/
#guard_msgs in
#certify_structural checkPartial

def slowId (n : Nat) : Nat := n
@[implemented_by slowId] def fastId (n : Nat) : Nat := n
def checkImpl (n : Nat) : Bool := fastId n == n

/--
error: R3 fails: the evaluation path of checkImpl reaches 1 constant(s) R3 forbids:
• fastId [this file]: @[implemented_by]: the compiled code is not the definition
    via [checkImpl, fastId]
-/
#guard_msgs in
#certify_structural checkImpl

-- A stand-in for Mathlib's `Finset.card`, to watch R1 report without Mathlib.
def Finset.card (l : List Nat) : Nat := l.length
def enumAll (k : Nat) : List Nat := List.range (2 ^ k)
def fuelFor (k : Nat) : Nat := Finset.card (enumAll k) + 1

/--
warning: R1 reports: the evaluation path of fuelFor counts or builds a domain at run time (1 site(s)); pass a cheap bound instead:
• Finset.card [this file]: materialises or counts a domain
    via [fuelFor, Finset.card]
-/
#guard_msgs in
#certify_domain fuelFor
/-- info: R1: nothing to report on checkS -/
#guard_msgs in
#certify_domain checkS

/--
info: R4 passes: checkS depends on [] ⊆ [propext, Quot.sound]
-/
#guard_msgs in
#certify_axioms checkS
theorem usesChoice : ∃ n : Nat, n = n := Classical.choice ⟨⟨0, rfl⟩⟩
/--
error: R4 fails: usesChoice depends on [Classical.choice], outside the allow-list [propext, Quot.sound]
-/
#guard_msgs in
#certify_axioms usesChoice

def wfLex : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, m => wfLex n (m + 1) + wfLex 0 m
termination_by n m => (n, m)

def checkLex (n : Nat) : Bool := wfLex n 0 == 0

/--
error: R3 fails: the evaluation path of checkLex reaches 1 constant(s) R3 forbids:
• wfLex._unary [this file]: auxiliary of a definition by well-founded recursion
    via [checkLex, wfLex, wfLex._unary]
-/
#guard_msgs in
#certify_structural checkLex

/-! A `match` that picks a few of many constructors compiles to a
`_sparseCasesOn` auxiliary that tests constructor indices with `Nat.land`.
`Nat.land` is defined by well-founded recursion (`Nat.bitwise._unary`) but
the kernel evaluates it natively on literals, so it is a leaf of the walk.
Found on `decideG4` in lax-logic (2026-10-09). -/

inductive Shape | a | b | c | d | e | f | g | h

def pick : Shape → Bool
  | .c => true
  | .f => true
  | _ => false

def checkPick (s : Shape) : Bool := pick s

/--
info: R3 passes: the evaluation path of checkPick is structural
-/
#guard_msgs in
#certify_structural checkPick
example : checkPick .f = true := by decide +kernel

-- Entered as a root, `Nat.land` does show its well-founded definition.
/--
error: R3 fails: the evaluation path of Nat.land reaches 1 constant(s) R3 forbids:
• Nat.bitwise._unary [Init.Data.Nat.Bitwise.Basic]: auxiliary of a definition by well-founded recursion
    via [Nat.land, Nat.bitwise, Nat.bitwise._unary]
-/
#guard_msgs in
#certify_structural Nat.land

/-! The exemption is the kernel's list and nothing else: a user-defined
function of the same shape as `Nat.bitwise` (two arguments, well-founded
recursion on the first) is still rejected. -/

def myBitwise (f : Bool → Bool → Bool) (n m : Nat) : Nat :=
  if h : n = 0 ∧ m = 0 then 0
  else 2 * myBitwise f (n / 2) (m / 2) + (if f (n % 2 == 1) (m % 2 == 1) then 1 else 0)
termination_by (n + m)
decreasing_by omega

def myLand (n m : Nat) : Nat := myBitwise and n m

def checkMyLand (n : Nat) : Bool := myLand n 1 == 1

/--
error: R3 fails: the evaluation path of checkMyLand reaches 1 constant(s) R3 forbids:
• myBitwise._unary [this file]: auxiliary of a definition by well-founded recursion
    via [checkMyLand, myLand, myBitwise, myBitwise._unary]
-/
#guard_msgs in
#certify_structural checkMyLand
