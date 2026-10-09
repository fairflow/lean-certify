import LeanCertify

/-! Under `route := .native` the compiled code is what checks, so
`@[implemented_by]` on the path is an error again (v0.2, decision (b)). -/

def Harness.config : Harness.Config := { route := .native }

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
