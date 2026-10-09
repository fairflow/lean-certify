/-
# Certifiers, verdicts and engines

The interface of `docs/outline.md` §5. A `Certifier` bundles a Boolean
checker with its soundness theorem; `Certifier.verdict` is the kernel gate.
Nothing here mentions a budget except `Engine.produce` (untrusted) and
`Engine.Complete` (optional, never needed for a verdict).

`Holds` is Sort-polymorphic (decision 5): a proposition (`u = 0`), or a type
of derivations (`u = 1`), in which case `sound` is a definition that builds
the derivation from the certificate.
-/

namespace Certify

universe u

/-- A certifier: a Boolean checker and its soundness theorem. -/
structure Certifier (Spec Cert : Type) (Holds : Spec → Sort u) where
  check : Spec → Cert → Bool
  sound : ∀ s c, check s c = true → Holds s

/-- The three-valued verdict of an untrusted producer. `fail` carries a
refutation certificate; an exhausted budget is `flag`, never `fail`. -/
inductive Verdict (Cert RCert : Type) where
  /-- A certificate for `Holds s`. -/
  | pass (c : Cert)
  /-- A certificate against `Holds s`. -/
  | fail (r : RCert)
  /-- Budget exhausted: rerun at a raised budget; never dropped. -/
  | flag
  deriving Repr

/-- An engine: a certifier for the property, one against it, and an
untrusted producer taking a budget at call time. -/
structure Engine (Spec Cert RCert : Type) (Holds : Spec → Sort u) where
  yes : Certifier Spec Cert Holds
  no : Certifier Spec RCert (fun s => Holds s → False)
  produce : Spec → Nat → Verdict Cert RCert

variable {Spec Cert RCert : Type} {Holds : Spec → Sort u}

/-- Optional: completeness of the producer. A budget appears here and
nowhere else. -/
def Engine.Complete (E : Engine Spec Cert RCert Holds) : Prop :=
  ∀ s, Holds s → ∃ n c, E.produce s n = .pass c

/-- Optional: a refinement. On a validated certificate a fast evaluator
agrees with the specification evaluator. -/
structure Refinement (Spec Cert Q : Type) (specEval : Spec → Q → Bool) where
  valid : Spec → Cert → Bool
  fastEval : Cert → Q → Bool
  refine : ∀ s c q, valid s c = true → fastEval c q = specEval s q

/-- The kernel gate: the checker's verdict carried to the property. The
Boolean is reduced by the kernel unless a proof is supplied. -/
def Certifier.verdict (K : Certifier Spec Cert Holds) (s : Spec) (c : Cert)
    (h : K.check s c = true := by decide +kernel) : Holds s :=
  K.sound s c h

/-- The empty certifier: no certificates, nothing to prove. With
`RCert := Empty` it is the `no` side of an engine without a refutation side
(decision 7). -/
def Certifier.empty : Certifier Spec Empty Holds where
  check _ c := nomatch c
  sound _ c := nomatch c

end Certify
