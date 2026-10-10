/-
# Chunking and streaming (V2, A)

`docs/v2-statements.md` A, approved by Matthew (R10, 2026-10-10). One long
`List.all` is checked chunk by chunk, each chunk by its own
`decide +kernel`, and the chunks are joined by `all_of_chunks` (locus's
lemma from `Logic/Examples/ABPCert.lean`, stated once here).

* `certify_chunks N for l by f size n from a to b` emits, for `a ≤ k < b`,
  `theorem N.chunk_k : ((l.drop (n * k)).take n).all f = true`.
* `certify_all N for l by f size n` computes `m := ⌈l.length / n⌉`, and
  emits `N.len : l.length ≤ n * m` and `N : l.all f = true`. It fails if a
  chunk theorem is missing.

**Streaming** is the same commands over several files. Each file proves a
range of chunks, and one file that imports them all assembles the result.
Each kernel check stays within one process's budget. `l` and `f` are
constants. Without `size`, the size is `@[harness chunkSize := some n]` on `l`,
then `Harness.config.chunkSize`.
-/
import LeanCertify.Config

open Lean Elab Command Meta

namespace Certify

universe u

/-- **`List.all`, chunk by chunk.** -/
theorem all_of_chunks {β : Type u} (f : β → Bool) (n : Nat) :
    ∀ (m : Nat) (l : List β), l.length ≤ n * m →
      (∀ k < m, ((l.drop (n * k)).take n).all f = true) → l.all f = true := by
  intro m
  induction m with
  | zero =>
    intro l hl _
    rw [List.eq_nil_of_length_eq_zero (by omega : l.length = 0)]
    rfl
  | succ m ih =>
    intro l hl hk
    rw [← List.take_append_drop n l, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using hk 0 (by omega), ih _ (by simp; rw [Nat.mul_succ] at hl; omega) ?_⟩
    intro k hk'
    have h := hk (k + 1) (by omega)
    rw [List.drop_drop]
    rwa [Nat.mul_succ, Nat.add_comm] at h

/-- Bounded quantification, one case at a time (the assembly step). -/
theorem forall_lt_zero (P : Nat → Prop) : ∀ k < 0, P k :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem forall_lt_succ {P : Nat → Prop} {m : Nat} (h : ∀ k < m, P k) (hm : P m) :
    ∀ k < m + 1, P k := fun k hk =>
  if he : k = m then he ▸ hm else h k (by omega)

namespace Chunk

/-- The chunk size: given, else the override on `l`, else the project's. -/
def sizeFor (l : Name) (given : Option Nat) : CommandElabM Nat := do
  if let some n := given then return n
  if let some n := (Harness.certifierConfigOf (← getEnv) l).chunkSize then return n
  if let some n := (← liftTermElabM Harness.readConfig).chunkSize then return n
  throwError "no chunk size: give `size n`, `@[harness chunkSize := some n]` on \
    {.ofConstName l}, or `Harness.config.chunkSize`"

/-- The name of chunk `k` of `N`. -/
def chunkName (N : Name) (k : Nat) : Name := N.str s!"chunk_{k}"

end Chunk

/-- Prove chunks `a ≤ k < b` of `l.all f = true`. -/
syntax (name := certifyChunks) "certify_chunks " ident " for " ident " by " ident
  (" size " num)? " from " num " to " num : command

/-- Assemble the chunks into `N : l.all f = true`. -/
syntax (name := certifyAll) "certify_all " ident " for " ident " by " ident
  (" size " num)? : command

@[command_elab certifyChunks] def elabChunks : CommandElab
  | `(certify_chunks $N for $l by $f $[size $n?]? from $a to $b) => do
    let lN ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo l
    let n ← Chunk.sizeFor lN (n?.map (·.getNat))
    if n == 0 then throwError "the chunk size must be positive"
    for k in [a.getNat:b.getNat] do
      let name := mkIdent (Chunk.chunkName N.getId k)
      let nl := Syntax.mkNumLit (toString n)
      let kl := Syntax.mkNumLit (toString k)
      elabCommand (← `(theorem $name : ((($l).drop ($nl * $kl)).take $nl).all $f = true := by
        decide +kernel))
  | _ => throwUnsupportedSyntax

@[command_elab certifyAll] def elabAll : CommandElab
  | `(certify_all $N for $l by $f $[size $n?]?) => do
    let lN ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo l
    let n ← Chunk.sizeFor lN (n?.map (·.getNat))
    if n == 0 then throwError "the chunk size must be positive"
    let len ← liftTermElabM do
      let e ← Term.elabTerm (← `(List.length $l)) (some (mkConst ``Nat))
      Term.synthesizeSyntheticMVarsNoPostponing
      unsafe evalExpr Nat (mkConst ``Nat) (← instantiateMVars e)
    let m := (len + n - 1) / n
    let nl := Syntax.mkNumLit (toString n)
    let ml := Syntax.mkNumLit (toString m)
    let mut missing := #[]
    for k in [0:m] do
      try discard <| liftCoreM <| realizeGlobalConstNoOverload (mkIdent (Chunk.chunkName N.getId k))
      catch _ => missing := missing.push k
    unless missing.isEmpty do
      throwError "certify_all {N.getId}: {l.getId} has {len} rows, {m} chunk(s) of size {n}; \
        no theorem for chunk(s) {missing.toList} (prove them with certify_chunks)"
    let lenId := mkIdent (N.getId.str "len")
    elabCommand (← `(theorem $lenId : ($l).length ≤ $nl * $ml := by decide +kernel))
    -- The bounded quantifier, built one chunk at a time.
    let P ← `(fun k => ((($l).drop ($nl * k)).take $nl).all $f = true)
    let mut acc ← `(Certify.forall_lt_zero $P)
    for k in [0:m] do
      let ck := mkIdent (Chunk.chunkName N.getId k)
      let kl := Syntax.mkNumLit (toString k)
      acc ← `(Certify.forall_lt_succ (P := $P) (m := $kl) $acc $ck)
    elabCommand (← `(theorem $N : ($l).all $f = true :=
      Certify.all_of_chunks $f $nl $ml $l $lenId $acc))
  | _ => throwUnsupportedSyntax

end Certify
