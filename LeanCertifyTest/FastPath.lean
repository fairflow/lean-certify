import LeanCertify

/-! `@[csimp]` fast paths (V2, B), watched passing and failing. -/

open Certify

/-- Specification: is `q` among the first `s` squares? (A linear search.) -/
def isSquareBelow (s q : Nat) : Bool := (List.range s).any fun k => k * k == q

/-- Certificate: the list of squares below `s`, precomputed. The fast
evaluator looks `q` up in it; the trace shows which path ran. -/
def sqRefinement : Refinement Nat (List Nat) Nat isSquareBelow where
  valid s c := c == (List.range s).map fun k => k * k
  dom _ _ _ := true
  fastEval _ c q := dbgTrace "fast path" fun _ => c.contains q
  refine s c q hv _ := by
    have hc : c = (List.range s).map fun k => k * k := by simpa using hv
    subst hc
    unfold dbgTrace isSquareBelow
    rw [Bool.eq_iff_iff]
    simp only [List.contains_iff_mem, List.mem_map, List.any_eq_true, beq_iff_eq]

certify_fastpath sqBelow from sqRefinement

/-- info: 'sqBelow.eq_fast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sqBelow.eq_fast

-- The kernel reads the specification.
example : sqBelow 10 ((List.range 10).map fun k => k * k) 49 = true := by decide +kernel

-- Compiled code runs the fast evaluator (the trace prints) on a valid certificate…
/--
info: fast path
---
info: true
-/
#guard_msgs in
#eval sqBelow 10 ((List.range 10).map fun k => k * k) 49

-- …and the specification on an invalid one (no trace).
/-- info: true -/
#guard_msgs in
#eval sqBelow 10 [] 49

-- Failing: not a refinement.
def notOne : Nat := 3
/--
error: certify_fastpath: notOne is not a Certify.Refinement (its type is Nat)
-/
#guard_msgs in
certify_fastpath bad from notOne
