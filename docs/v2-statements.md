# Lean certify V2: statements for review (R10)

For Matthew, 2026-10-10, on branch `v2`. Everything below is OPEN until you
approve it or supply an alternative; no proof has been written. The two items
already decided for v0.2 are built on the branch: (b) R3 under the kernel
route, and (c) the new shape of `Refinement` (see the end of this document).

V2 proper is the outline's queue (§9): `@[csimp]` refinement equations, and
streaming beyond chunking. Release: 0.2.0, a minor release, because (c)
changes a signature; it will ship a migration note.

## A. Chunking and streaming (`LeanCertify/Chunk.lean`)

```lean
theorem Certify.all_of_chunks {β : Type u} (f : β → Bool) (n : Nat) :
    ∀ (m : Nat) (l : List β), l.length ≤ n * m →
      (∀ k < m, ((l.drop (n * k)).take n).all f = true) → l.all f = true
```

This is locus's `all_of_chunks` (`Logic/Examples/ABPCert.lean`), stated once
in the library. Two commands generate what locus now writes by hand (the
14-case `match` in `tcert₁_ok`):

```lean
certify_chunks N for l by f size n from a to b
-- emits, for each k with a ≤ k < b:
--   theorem N.chunk_k : ((l.drop (n * k)).take n).all f = true := by decide +kernel

certify_all N for l by f size n
-- computes m := ⌈l.length / n⌉ at elaboration time, and emits
--   theorem N.len : l.length ≤ n * m := by decide +kernel
--   theorem N : l.all f = true := Certify.all_of_chunks f n m l N.len (fun k hk => …N.chunk_k…)
-- an error if some N.chunk_k is missing.
```

**Streaming** is the same pair of commands over several files. Each file
runs `certify_chunks` on a range of `k`, and one file imports them all and
runs `certify_all`. Each kernel check stays within one process's budget
(the 4 GB / 30 s rule), and the files build in parallel. `l` and `f` are
constants (generated certificate data). `size n` may be omitted, in which
case it defaults to the certifier's `chunkSize` override, then to
`Harness.config.chunkSize`.

## B. `@[csimp]` fast paths (`LeanCertify/FastPath.lean`)

```lean
/-- Fast on a validated certificate within the domain, the specification
    otherwise. -/
def Certify.Refinement.guarded (R : Refinement Spec Cert Q specEval)
    (s : Spec) (c : Cert) (q : Q) : Bool :=
  if R.valid s c && R.dom s c q then R.fastEval s c q else specEval s q

theorem Certify.Refinement.guarded_eq (R : Refinement Spec Cert Q specEval) :
    R.guarded = fun s _ q => specEval s q
```

The guard turns the conditional refinement into an unconditional equation,
which is the form `@[csimp]` needs. The command:

```lean
certify_fastpath N from R
-- emits
--   def N (s : Spec) (c : Cert) (q : Q) : Bool := specEval s q     -- the kernel's meaning
--   def N.fast (s : Spec) (c : Cert) (q : Q) : Bool := R.guarded s c q
--   @[csimp] theorem N.eq_fast : @N = @N.fast                     -- from guarded_eq
```

One definition, `N`, then serves both routes. The kernel reduces `N` to
`specEval`; compiled code runs `N.fast`, the fast evaluator whenever the
certificate validates. Prototyped by hand with the proofs left as
placeholders: `#eval N 3 () 9` ran the fast evaluator (its trace printed),
and `example : N 3 () 9 = true := by decide +kernel` checked by the
specification.

The cost: `N.fast` re-runs `R.valid s c` on every call. A caller that has
already validated can call `R.fastEval` directly.

For a plain checker (`check` and a faster `checkFast` with
`@check = @checkFast` proved), Lean's own `@[csimp]` already suffices. The
harness adds nothing except documentation in `SKILL.md`.

## Not proposed for V2

- A batch driver for producers (R5 reruns, R7 deadlines, R8 timing):
  approved as a V2 candidate (screening note), but it is an executable with
  process control, not library Lean. I suggest it as V3, or a separate
  tool, if you want it.
- The `RankBudgetSuffices` example: not started, as decided.

## Already built on the branch (decided 2026-10-09)

- (b) R3: under `route := .kernel`, `@[implemented_by]` on the path is an
  information note; under any other route it is an error. Tests:
  `LeanCertifyTest/Lint.lean`, `LeanCertifyTest/RouteNative.lean`.
- (c) `Refinement`: `fastEval : Spec → Cert → Q → Bool`,
  `dom : Spec → Cert → Q → Bool`, `refine : ∀ s c q, valid s c = true →
  dom s c q = true → fastEval s c q = specEval s q`.

Migration note (draft, for 0.2.0): `Refinement` users add `dom` (use
`fun _ _ _ => true` for the old meaning) and give `fastEval` a first
argument `_ : Spec`. Locus's pinned R3 error on `Match.guard` becomes an
information line; update its `#guard_msgs` when locus moves to 0.2.
