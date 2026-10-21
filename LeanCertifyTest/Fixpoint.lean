import LeanCertify

/-! The table certifier for `partial_fixpoint` functions (`LeanCertify/Fixpoint.lean`),
watched passing and failing.

Two functions the kernel cannot evaluate: `collatz` (tail recursion, nobody
knows that it terminates) and `ack` (Ackermann's function with a nested
call, through `Option`'s `bind`). For each: the body `F` written out, its
monotonicity (`repeat monotonicity`), its unfolding equation, an untrusted
producer that records calls in post-order, and certified facts. -/

open Lean.Order Certify Certify.Fixpoint

/-! ### `collatz` -/

/-- The Collatz iteration, counting steps. -/
def collatz (n k : Nat) : Option Nat :=
  if n ≤ 1 then some k
  else if n % 2 = 0 then collatz (n / 2) (k + 1) else collatz (3 * n + 1) (k + 1)
partial_fixpoint

/-- The body, uncurried, with the recursive call abstracted. -/
def collatzF (rec : Nat × Nat → Option Nat) (p : Nat × Nat) : Option Nat :=
  if p.1 ≤ 1 then some p.2
  else if p.1 % 2 = 0 then rec (p.1 / 2, p.2 + 1) else rec (3 * p.1 + 1, p.2 + 1)

theorem collatzF_mono : monotone collatzF := by
  unfold collatzF
  repeat monotonicity

/-- `collatz` is a fixed point of its body: its unfolding equation. -/
theorem collatz_fixed : ∀ p, collatzF (fun q => collatz q.1 q.2) p = collatz p.1 p.2 := by
  intro ⟨n, k⟩
  conv => rhs; rw [collatz.eq_1]
  rfl

def collatzCert := certifier collatzF collatzF_mono

/-- info: R3 passes: the evaluation path of collatzCert is structural -/
#guard_msgs in #certify_structural collatzCert
/-- info: R2 passes: the property of collatzCert mentions no budget -/
#guard_msgs in #certify_statement collatzCert
/-- info: R4 passes: collatzCert depends on [propext, Quot.sound] ⊆ [propext, Quot.sound] -/
#guard_msgs in #certify_axioms collatzCert

/-- The producer: the iteration, recording the arguments; every call returns
the final count, and the calls return innermost first (post-order). -/
partial def collatzTable (n k : Nat) : List ((Nat × Nat) × Nat) :=
  let rec go (n k : Nat) (args : List (Nat × Nat)) : List (Nat × Nat) × Nat :=
    if n ≤ 1 then ((n, k) :: args, k)
    else if n % 2 = 0 then go (n / 2) (k + 1) ((n, k) :: args)
    else go (3 * n + 1) (k + 1) ((n, k) :: args)
  let (args, r) := go n k []
  args.map (·, r)

#guard collatzTable 4 0 == [((1, 2), 2), ((2, 1), 2), ((4, 0), 2)]

/-- The certified fact: every fixed point of the body sends `(4, 0)` to `2`.
Choice-free. -/
theorem collatz_4_fixes : FixesAt collatzF (4, 0) 2 :=
  collatzCert.verdict ((4, 0), 2) [((1, 2), 2), ((2, 1), 2), ((4, 0), 2)]

/-- info: 'collatz_4_fixes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms collatz_4_fixes

/--
info: R3 passes: the evaluation path of collatz_4_fixes, walked from what its proof decides by evaluation:
  collatzCert.check ((4, 0), 2) [((1, 2), 2), ((2, 1), 2), ((4, 0), 2)] = true
is structural
-/
#guard_msgs in #certify_structural collatz_4_fixes

/-- The fact about `collatz` itself. It mentions `collatz`, whose definition
is a least fixpoint built with `Classical.choice`, so it depends on
`Classical.choice`; no certificate can remove that. -/
theorem collatz_4 : collatz 4 0 = some 2 := collatz_4_fixes _ collatz_fixed

/-- info: 'collatz_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms collatz_4

-- The kernel cannot evaluate `collatz` itself: `decide` and `rfl` fail.
example : collatz 4 0 = some 2 := by
  fail_if_success decide
  fail_if_success rfl
  exact collatz_4

/-! ### Negative tests -/

/-- Order matters. Every function is a fixed point of the identity body, and
the least is `fun _ => none`; so `[(0, 5)]` certifies nothing, though its
entry reproduces itself if it may read itself. -/
def idF (g : Nat → Option Nat) : Nat → Option Nat := g

theorem idF_mono : monotone idF := fun _ _ h => h

theorem not_fixesAt_id : ¬ FixesAt idF 0 5 := by
  intro h
  have := h (fun _ => none) (fun _ => rfl)
  cases this

-- The entry reproduces itself if it may read itself …
example : idF (lookup [(0, 5)]) 0 = some 5 := rfl
-- … but not from the entries before it, so the check rejects it.
example : check idF [(0, 5)] = false := by decide

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (certifier idF idF_mono).check (0, 5) [(0, 5)] = true
is false
-/
#guard_msgs in
example : FixesAt idF 0 5 := (certifier idF idF_mono).verdict (0, 5) [(0, 5)]

-- A wrong value is rejected.
example : check collatzF [((1, 2), 2), ((2, 1), 2), ((4, 0), 3)] = false := by decide
-- A missing entry gives a failed check, never a wrong theorem: the call
-- `(2, 1)` reads `none`.
example : check collatzF [((1, 2), 2), ((4, 0), 2)] = false := by decide
-- The specification must be in the table.
example : collatzCert.check ((2, 1), 2) [((1, 2), 2), ((4, 0), 2)] = false := by decide

/-! ### `ack`: a nested call -/

/-- Ackermann's function. Total, but written as a `partial_fixpoint` it is as
opaque to the kernel as `collatz`. -/
def ack (m n : Nat) : Option Nat :=
  if m = 0 then some (n + 1)
  else if n = 0 then ack (m - 1) 1
  else do
    let r ← ack m (n - 1)
    ack (m - 1) r
partial_fixpoint

def ackF (rec : Nat × Nat → Option Nat) (p : Nat × Nat) : Option Nat :=
  if p.1 = 0 then some (p.2 + 1)
  else if p.2 = 0 then rec (p.1 - 1, 1)
  else do
    let r ← rec (p.1, p.2 - 1)
    rec (p.1 - 1, r)

theorem ackF_mono : monotone ackF := by
  unfold ackF
  repeat monotonicity

theorem ack_fixed : ∀ p, ackF (fun q => ack q.1 q.2) p = ack p.1 p.2 := by
  intro ⟨m, n⟩
  conv => rhs; rw [ack.eq_1]
  rfl

def ackCert := certifier ackF ackF_mono

/-- The producer: memoised, each call recorded when it returns. -/
partial def ackTable (m n : Nat) (T : List ((Nat × Nat) × Nat)) :
    Nat × List ((Nat × Nat) × Nat) :=
  match lookup T (m, n) with
  | some v => (v, T)
  | none =>
    if m = 0 then (n + 1, ((m, n), n + 1) :: T)
    else if n = 0 then
      let (v, T) := ackTable (m - 1) 1 T
      (v, ((m, n), v) :: T)
    else
      let (r, T) := ackTable m (n - 1) T
      let (v, T) := ackTable (m - 1) r T
      (v, ((m, n), v) :: T)

#guard (ackTable 2 3 []).2.reverse ==
  [((0, 1), 2), ((1, 0), 2), ((0, 2), 3), ((1, 1), 3), ((2, 0), 3), ((0, 3), 4), ((1, 2), 4),
   ((0, 4), 5), ((1, 3), 5), ((2, 1), 5), ((0, 5), 6), ((1, 4), 6), ((0, 6), 7), ((1, 5), 7),
   ((2, 2), 7), ((0, 7), 8), ((1, 6), 8), ((0, 8), 9), ((1, 7), 9), ((2, 3), 9)]

theorem ack_2_3_fixes : FixesAt ackF (2, 3) 9 :=
  ackCert.verdict ((2, 3), 9)
    [((0, 1), 2), ((1, 0), 2), ((0, 2), 3), ((1, 1), 3), ((2, 0), 3), ((0, 3), 4), ((1, 2), 4),
     ((0, 4), 5), ((1, 3), 5), ((2, 1), 5), ((0, 5), 6), ((1, 4), 6), ((0, 6), 7), ((1, 5), 7),
     ((2, 2), 7), ((0, 7), 8), ((1, 6), 8), ((0, 8), 9), ((1, 7), 9), ((2, 3), 9)]

theorem ack_2_3 : ack 2 3 = some 9 := ack_2_3_fixes _ ack_fixed

/-- info: 'ack_2_3_fixes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ack_2_3_fixes

/-! ### Facts about the subject: an invariant, choice-free

`n < ack m n`, proved once for one step of the body (the premise of
`ack.partial_correctness`), then certified per table, without `ack` and
without `Classical.choice`. -/

theorem ackF_grows (g : Nat × Nat → Option Nat)
    (hg : ∀ x r, g x = some r → x.2 < r) : ∀ x r, ackF g x = some r → x.2 < r := by
  intro ⟨m, n⟩ r h
  simp only [ackF] at h
  split at h
  · cases h; exact Nat.lt_succ_self n
  · split at h
    · next hn => have := hg _ _ h; simp only at this ⊢; omega
    · next hn =>
      cases h1 : g (m, n - 1) with
      | none => rw [h1] at h; cases h
      | some r1 =>
        rw [h1] at h
        have := hg _ _ h1
        have := hg _ _ h
        simp only at *
        omega

def ackGrows := specCertifier ackF (fun x r => x.2 < r) ackF_grows

/-- `3 < 9`, read off the table of `ack 2 3`, about Ackermann's function as
the body describes it; no `ack`, no choice. -/
theorem ack_2_3_grows : 3 < 9 :=
  ackGrows.verdict ((2, 3), 9)
    [((0, 1), 2), ((1, 0), 2), ((0, 2), 3), ((1, 1), 3), ((2, 0), 3), ((0, 3), 4), ((1, 2), 4),
     ((0, 4), 5), ((1, 3), 5), ((2, 1), 5), ((0, 5), 6), ((1, 4), 6), ((0, 6), 7), ((1, 5), 7),
     ((2, 2), 7), ((0, 7), 8), ((1, 6), 8), ((0, 8), 9), ((1, 7), 9), ((2, 3), 9)]

/-- The same lemma proves partial correctness of `ack` itself (with choice,
through `ack`). -/
theorem ack_grows (m n r : Nat) (h : ack m n = some r) : n < r :=
  ack.partial_correctness (motive := fun _ n r => n < r)
    (fun ack' ih m n r h => ackF_grows (fun q => ack' q.1 q.2)
      (fun x r h => ih x.1 x.2 r h) (m, n) r h) m n r h

/-- info: 'ack_2_3_grows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ack_2_3_grows
/-- info: 'ack_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ack_grows
/-- info: 'ack_2_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ack_2_3

/-! ### The library's theorems -/

/-- info: 'Certify.Fixpoint.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_sound
/-- info: 'Certify.Fixpoint.check_spec' depends on axioms: [propext] -/
#guard_msgs in #print axioms check_spec
/--
info: 'Certify.Fixpoint.fixesAt_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms fixesAt_iff
