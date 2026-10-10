import LeanCertify
/-! The library's theorems, axioms pinned (R4). -/
/-- info: 'Certify.all_of_chunks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Certify.all_of_chunks
/-- info: 'Certify.forall_lt_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Certify.forall_lt_succ
/-- info: 'Certify.forall_lt_zero' does not depend on any axioms -/
#guard_msgs in #print axioms Certify.forall_lt_zero
/-- info: 'Certify.Refinement.guarded_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Certify.Refinement.guarded_eq
