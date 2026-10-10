import LeanCertify
/-! Certificate data for the chunking tests: 50 rows, every one even. -/
def rows : List Nat := (List.range 50).map (2 * ·)
def evenB (n : Nat) : Bool := n % 2 == 0
