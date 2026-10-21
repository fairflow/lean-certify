/-
# Facts about `partial_fixpoint` functions, certified by a table (v0.3.1)

**Why this exists.** The kernel cannot evaluate a function defined by
`partial_fixpoint`: its value is `Lean.Order.fix F _`, a least fixpoint
built with `Classical.choice`, so `decide` and `rfl` fail on
`collatz 4 0 = some 2` (and R3 reports `Lean.Order.fix`). Yet the compiled
code runs fast, and the definition comes with an unfolding equation, which a
`partial def` does not. This certifier joins the two: the compiled function
produces a table, and the kernel evaluates the *body* `F` on the table's
entries, never the fixpoint.

**The check.** A table `T` is a list of pairs `(a, b)`. It passes if each
entry is reproduced by one application of the body, the recursive calls
answered from the entries before it (`lookup`; a call with no earlier entry
answers `none`):

    ∀ i < T.length, F (lookup (T.take i)) T[i].1 = some T[i].2

(`checkFrom` keeps the earlier entries newest first, so `lookup` returns the
latest earlier entry for a key; every earlier entry is a proved fact, so
either is sound.)

**The theorem** (`check_sound`): if the check passes, then for every entry
`(a, b)`, `FixesAt F a b`, that is

    ∀ f, (∀ x, F f x = f x) → f a = some b,

every fixed point of `F` sends `a` to `some b`. Proof: induction along the
table. The earlier entries lie below `f` in the flat order of `Option`
(`none` below everything; `lookup_le`), `F` is monotone, so
`F (lookup done) ⊑ F f = f`, and `some b ⊑ y` forces `y = some b`
(`some_le`). Only the fixed-point equation is used, never leastness, so
`FixesAt` mentions no fixpoint operator and the whole certifier is free of
`Classical.choice`.

**Nothing is lost** (`fixesAt_iff`): for monotone `F`, `FixesAt F a b` holds
exactly when `Lean.Order.fix F hF a = some b`, the value `partial_fixpoint`
defines (the least fixed point lies below every fixed point, and in the flat
order `some b` has nothing above it). For a `partial_fixpoint` function `f`
with body `F`, applying a certified `FixesAt F a b` to `f` and its
unfolding equation gives `f a = some b`. That last step, and every theorem
whose statement mentions `f`, depends on `Classical.choice`, through `f`
itself (`Lean.Order.fix`); the certificate check and the `FixesAt` facts
do not.

**Facts about the subject** (`check_spec`, `specCertifier`). The same
table certifies an invariant `P` of the answers, given the one-step
preservation lemma that `partial_correctness` takes as its premise:

    (∀ g, (∀ x r, g x = some r → P x r) → ∀ x r, F g x = some r → P x r)
      → check F T = true → ∀ (a, b) ∈ T, P a b

The same induction along the table, with no fixpoint and no monotonicity.
The premise is exactly what `f.partial_correctness` asks for, so one proof
about the body gives both a theorem about the compiled function `f` and, per
table, certified facts. For a search returning `some true` / `some false`,
with `P s true` "derivable" and `P s false` "not derivable", those are facts
about the logic itself, free of `Classical.choice`, from a producer nobody
proved terminating. That is the room `partial_fixpoint` gives over
`partial def`, whose body one cannot reason about at all.

**Order matters.** An entry may use only the entries before it. With
`F g = g`, every function is a fixed point and the least is `fun _ => none`,
yet the table `[(0, 5)]` would reproduce itself if an entry could see itself
(`LeanCertifyTest/Fixpoint.lean`, `not_fixesAt_id`).

**Cost.** One evaluation of the body per entry, plus the lookups, which are
linear in the table: quadratic in all. The table has one entry per distinct
call the producer made. Measured in `LeanCertifyTest/FixpointScale.lean`.

**The producer** is untrusted: typically the compiled function itself,
recording each call when it returns (post-order), which gives the order the
check needs, and memoising if calls repeat.
-/
import LeanCertify.Certifier

open Lean.Order

namespace Certify.Fixpoint

variable {α β : Type}

/-- The value the table records for `a`: the first entry with key `a`. -/
def lookup [DecidableEq α] : List (α × β) → α → Option β
  | [], _ => none
  | (x, y) :: t, a => if x = a then some y else lookup t a

/-- Check the entries in order. `done` holds the entries already checked,
newest first; each entry must be reproduced by one application of `F` that
reads only `done`. -/
def checkFrom [DecidableEq α] [DecidableEq β] (F : (α → Option β) → α → Option β)
    (done : List (α × β)) : List (α × β) → Bool
  | [] => true
  | (a, b) :: rest => decide (F (lookup done) a = some b) && checkFrom F ((a, b) :: done) rest

/-- The table check: every entry is reproduced from the entries before it. -/
def check [DecidableEq α] [DecidableEq β] (F : (α → Option β) → α → Option β)
    (T : List (α × β)) : Bool :=
  checkFrom F [] T

/-- Every fixed point of `F` sends `a` to `some b`. -/
def FixesAt (F : (α → Option β) → α → Option β) (a : α) (b : β) : Prop :=
  ∀ f : α → Option β, (∀ x, F f x = f x) → f a = some b

/-- In the flat order of `Option`, nothing lies strictly above `some b`. -/
theorem some_le {b : β} {y : Option β} (h : some b ⊑ y) : y = some b := by
  cases h <;> rfl

/-- A table of true entries lies below `f`. -/
theorem lookup_le [DecidableEq α] {f : α → Option β} {done : List (α × β)}
    (h : ∀ p ∈ done, f p.1 = some p.2) : lookup done ⊑ f := by
  intro x
  induction done with
  | nil => exact FlatOrder.rel.bot
  | cons p t ih =>
    obtain ⟨y, b⟩ := p
    simp only [lookup]
    split
    · next hy =>
      subst hy
      exact (h (y, b) (List.mem_cons_self ..)) ▸ PartialOrder.rel_refl
    · exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- The induction along the table, for one fixed point `f`. -/
theorem checkFrom_sound [DecidableEq α] [DecidableEq β] {F : (α → Option β) → α → Option β}
    (hF : monotone F) {f : α → Option β} (hf : ∀ x, F f x = f x) :
    ∀ (T done : List (α × β)), (∀ p ∈ done, f p.1 = some p.2) →
      checkFrom F done T = true → ∀ p ∈ T, f p.1 = some p.2 := by
  intro T
  induction T with
  | nil => intro _ _ _ p hp; cases hp
  | cons e rest ih =>
    obtain ⟨a, b⟩ := e
    intro done hdone hc
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨he, hrest⟩ := hc
    have hab : f a = some b := by
      have hle : F (lookup done) a ⊑ F f a := hF _ _ (lookup_le hdone) a
      rw [he, hf] at hle
      exact some_le hle
    have hdone' : ∀ p ∈ (a, b) :: done, f p.1 = some p.2 := by
      intro p hp
      cases hp with
      | head => exact hab
      | tail _ hp => exact hdone p hp
    intro p hp
    cases hp with
    | head => exact hab
    | tail _ hp => exact ih _ hdone' hrest p hp

/-- **Soundness of the table check**: every entry of a passing table holds
of every fixed point of `F`. -/
theorem check_sound [DecidableEq α] [DecidableEq β] {F : (α → Option β) → α → Option β}
    (hF : monotone F) {T : List (α × β)} (h : check F T = true) :
    ∀ p ∈ T, FixesAt F p.1 p.2 :=
  fun p hp _ hf => checkFrom_sound hF hf T [] (fun _ h => nomatch h) h p hp

/-- An entry `lookup` returns is in the table. -/
theorem lookup_mem [DecidableEq α] {done : List (α × β)} {x : α} {r : β}
    (h : lookup done x = some r) : (x, r) ∈ done := by
  induction done with
  | nil => cases h
  | cons p t ih =>
    obtain ⟨y, b⟩ := p
    simp only [lookup] at h
    split at h
    · next hy => cases h; subst hy; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

/-- The induction along the table, for an invariant `P`. -/
theorem checkFrom_spec [DecidableEq α] [DecidableEq β] {F : (α → Option β) → α → Option β}
    {P : α → β → Prop}
    (hP : ∀ g : α → Option β, (∀ x r, g x = some r → P x r) → ∀ x r, F g x = some r → P x r) :
    ∀ (T done : List (α × β)), (∀ p ∈ done, P p.1 p.2) →
      checkFrom F done T = true → ∀ p ∈ T, P p.1 p.2 := by
  intro T
  induction T with
  | nil => intro _ _ _ p hp; cases hp
  | cons e rest ih =>
    obtain ⟨a, b⟩ := e
    intro done hdone hc
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨he, hrest⟩ := hc
    have hab : P a b := hP (lookup done) (fun x r h => hdone (x, r) (lookup_mem h)) a b he
    have hdone' : ∀ p ∈ (a, b) :: done, P p.1 p.2 := by
      intro p hp
      cases hp with
      | head => exact hab
      | tail _ hp => exact hdone p hp
    intro p hp
    cases hp with
    | head => exact hab
    | tail _ hp => exact ih _ hdone' hrest p hp

/-- **Facts about the subject.** If one application of the body preserves an
invariant `P` (the premise of `partial_correctness`: answers read from calls
satisfying `P` give an answer satisfying `P`), every entry of a passing table
satisfies `P`. Neither monotonicity nor any fixed point is involved, so a
search proved correct step by step once gives, per table, facts about what
it searches (derivable, not derivable) free of `Classical.choice`. -/
theorem check_spec [DecidableEq α] [DecidableEq β] {F : (α → Option β) → α → Option β}
    {P : α → β → Prop}
    (hP : ∀ g : α → Option β, (∀ x r, g x = some r → P x r) → ∀ x r, F g x = some r → P x r)
    {T : List (α × β)} (h : check F T = true) : ∀ p ∈ T, P p.1 p.2 :=
  checkFrom_spec hP T [] (fun _ h => nomatch h) h

/-- `FixesAt F a b` is exactly the value of the least fixed point, the one
`partial_fixpoint` defines. Not used by the certifier; it shows that
certifying `FixesAt` loses nothing. Depends on `Classical.choice`, through
`Lean.Order.fix`. -/
theorem fixesAt_iff {F : (α → Option β) → α → Option β} (hF : monotone F) (a : α) (b : β) :
    FixesAt F a b ↔ fix F hF a = some b := by
  constructor
  · intro h
    exact h (fix F hF) fun x => (congrFun (fix_eq hF) x).symm
  · intro hfix g hg
    have hFg : F g = g := funext hg
    have hle : fix F hF ⊑ g := by
      apply fix_induct hF (· ⊑ g)
      · intro c hc hcg
        exact csup_le hc hcg
      · intro x hx
        exact hFg ▸ hF x g hx
    have := hle a
    rw [hfix] at this
    exact some_le this

/-- **The certifier**: a table certifies each of its entries. The
specification is a pair `(a, b)`; the certificate is a table containing it. -/
def certifier [DecidableEq α] [DecidableEq β] (F : (α → Option β) → α → Option β)
    (hF : monotone F) :
    Certifier (α × β) (List (α × β)) (fun s => FixesAt F s.1 s.2) where
  check s T := check F T && decide (s ∈ T)
  sound s T h := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact check_sound hF h.1 s h.2

/-- **The certifier for an invariant**: a table certifies `P a b` for each of
its entries `(a, b)`, given that one application of `F` preserves `P`. -/
def specCertifier [DecidableEq α] [DecidableEq β] (F : (α → Option β) → α → Option β)
    (P : α → β → Prop)
    (hP : ∀ g : α → Option β, (∀ x r, g x = some r → P x r) → ∀ x r, F g x = some r → P x r) :
    Certifier (α × β) (List (α × β)) (fun s => P s.1 s.2) where
  check s T := check F T && decide (s ∈ T)
  sound s T h := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact check_spec hP h.1 s h.2

end Certify.Fixpoint
