/-!
# Core `String` operations that leak `Classical.choice` (R4 documentation)

Pinned with `#guard_msgs`, so a toolchain that changes any of these fails the
build. Measured identical on v4.31.0 and v4.33.0 (2026-10-09; first found by
locus on v4.33). The leak is through core's UTF-8 decoding proofs. A
certified checker over strings should use only the clean operations:
`==`, `decide (s = t)`, `isEmpty`, `String.ofList`, `toByteArray`, and
`++` (which needs `propext` only).
-/

def toList' (s : String) := s.toList
def length' (s : String) := s.length
def trim' (s : String) := s.trimAscii
def contains' (s : String) := s.contains 'a'
def toLower' (s : String) := s.toLower
def splitOn' (s : String) := s.splitOn ","
def beq' (s t : String) := s == t
def decEq' (s t : String) := decide (s = t)
def isEmpty' (s : String) := s.isEmpty
def ofList' (l : List Char) := String.ofList l
def toByteArray' (s : String) := s.toByteArray
def append' (s t : String) := s ++ t

-- Leak `Classical.choice`.
/-- info: 'toList'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms toList'
/-- info: 'length'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms length'
/-- info: 'trim'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms trim'
/-- info: 'contains'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms contains'
/-- info: 'toLower'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms toLower'
/-- info: 'splitOn'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms splitOn'

-- Clean.
/-- info: 'beq'' does not depend on any axioms -/
#guard_msgs in #print axioms beq'
/-- info: 'decEq'' does not depend on any axioms -/
#guard_msgs in #print axioms decEq'
/-- info: 'isEmpty'' does not depend on any axioms -/
#guard_msgs in #print axioms isEmpty'
/-- info: 'ofList'' does not depend on any axioms -/
#guard_msgs in #print axioms ofList'
/-- info: 'toByteArray'' does not depend on any axioms -/
#guard_msgs in #print axioms toByteArray'
/-- info: 'append'' depends on axioms: [propext] -/
#guard_msgs in #print axioms append'
