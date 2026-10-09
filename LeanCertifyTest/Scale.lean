import LeanCertify
-- The shapes `FinCM.checkB` uses: membership of (Nat × String) pairs, range
-- folds. The R3 walk enters core and must not raise false alarms there.
def memB (val : List (Nat × String)) (w : Nat) (a : String) : Bool :=
  decide ((w, a) ∈ val) || (List.range 5).all fun v => v != w
/-- info: R3 passes: the evaluation path of memB is structural -/
#guard_msgs in
#certify_structural memB
example : memB [(1, "p")] 1 "p" = true := by decide +kernel
