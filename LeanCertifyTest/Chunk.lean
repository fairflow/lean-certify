import LeanCertifyTest.Stream.PartA
import LeanCertifyTest.Stream.PartB

/-! Chunking (V2, A), each command watched passing and failing. -/

-- Streaming: the chunks were proved in two other files; assemble here.
certify_all rowsEven for rows by evenB size 8

/-- info: 'rowsEven' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rowsEven

example : rows.all evenB = true := rowsEven

-- One file, size from the data's override.
@[harness chunkSize := some 16] def rows2 : List Nat := (List.range 40).map (4 * ·)
certify_chunks rows2Even for rows2 by evenB from 0 to 3
certify_all rows2Even for rows2 by evenB

-- Failing: a missing chunk.
certify_chunks gapped for rows by evenB size 10 from 0 to 4
/--
error: certify_all gapped: rows has 50 rows, 5 chunk(s) of size 10; no theorem for chunk(s) [4] (prove them with certify_chunks)
-/
#guard_msgs in
certify_all gapped for rows by evenB size 10

-- Failing: a false chunk (51 is odd).
def bad : List Nat := rows ++ [51]
/--
error: Tactic `decide` proved that the proposition
  (List.take 8 (List.drop (8 * 6) bad)).all evenB = true
is false
-/
#guard_msgs in
certify_chunks badEven for bad by evenB size 8 from 6 to 7

-- Failing: no size anywhere.
/--
error: no chunk size: give `size n`, `@[harness chunkSize := some n]` on rows, or `Harness.config.chunkSize`
-/
#guard_msgs in
certify_chunks nosize for rows by evenB from 0 to 1
