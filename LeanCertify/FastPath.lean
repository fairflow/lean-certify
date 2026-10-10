/-
# `@[csimp]` fast paths (V2, B)

`docs/v2-statements.md` B, approved by Matthew (R10, 2026-10-10). A
`Refinement` says that on a validated certificate, within its domain, a
fast evaluator agrees with the specification evaluator. Guarding the fast
evaluator by the validity test turns that conditional equation into an
unconditional one, `guarded_eq`, which is the form `@[csimp]` needs.

`certify_fastpath N from R` (with `R` a constant of type
`Refinement Spec Cert Q specEval`, without parameters) emits:

* `def N (s : Spec) (c : Cert) (q : Q) : Bool := specEval s q`: the
  kernel's meaning;
* `def N.fast (s : Spec) (c : Cert) (q : Q) : Bool := R.guarded s c q`;
* `@[csimp] theorem N.eq_fast : @N = @N.fast`.

The kernel then reduces `N` to `specEval`, while compiled code runs
`N.fast`, which is fast whenever the certificate validates. `N.fast`
re-runs `R.valid` on every call. A caller that has already validated may
call `R.fastEval` directly.
-/
import LeanCertify.Certifier
import Lean

open Lean Elab Command Meta

namespace Certify

variable {Spec Cert Q : Type} {specEval : Spec → Q → Bool}

/-- Fast on a validated certificate within the domain, the specification
otherwise. -/
def Refinement.guarded (R : Refinement Spec Cert Q specEval) (s : Spec) (c : Cert) (q : Q) :
    Bool :=
  if R.valid s c && R.dom s c q then R.fastEval s c q else specEval s q

/-- **The guarded evaluator is the specification**, unconditionally. -/
theorem Refinement.guarded_eq (R : Refinement Spec Cert Q specEval) :
    R.guarded = fun s _ q => specEval s q := by
  funext s c q
  unfold Refinement.guarded
  split
  · next h =>
    rw [Bool.and_eq_true] at h
    exact R.refine s c q h.1 h.2
  · rfl

/-- `certify_fastpath N from R`: one definition `N` serving the kernel (as
the specification) and compiled code (as the guarded fast evaluator). -/
syntax (name := certifyFastpath) "certify_fastpath " ident " from " ident : command

@[command_elab certifyFastpath] def elabFastpath : CommandElab
  | `(certify_fastpath $N from $R) => do
    let rN ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo R
    let ci ← getConstInfo rN
    unless ci.levelParams.isEmpty do
      throwError "certify_fastpath: {.ofConstName rN} has universe parameters; \
        give a concrete refinement"
    let ty ← liftTermElabM <| whnf ci.type
    let some (``Certify.Refinement) := ty.getAppFn.constName? |
      throwError "certify_fastpath: {.ofConstName rN} is not a Certify.Refinement \
        (its type is {ci.type})"
    let #[spec, cert, q, specEval] := ty.getAppArgs |
      throwError "certify_fastpath: unexpected type {ci.type}"
    let n := (← getCurrNamespace) ++ N.getId
    let fast := n.str "fast"
    let rConst := mkConst rN
    let evalTy := mkForall `s .default spec <| mkForall `c .default cert <|
      mkForall `q .default q (mkConst ``Bool)
    -- N := fun s c q => specEval s q
    let nVal := mkLambda `s .default spec <| mkLambda `c .default cert <|
      mkLambda `q .default q (mkApp2 specEval (.bvar 2) (.bvar 0))
    -- N.fast := fun s c q => R.guarded s c q
    let fVal := mkLambda `s .default spec <| mkLambda `c .default cert <|
      mkLambda `q .default q <|
        mkAppN (mkConst ``Certify.Refinement.guarded)
          #[spec, cert, q, specEval, rConst, .bvar 2, .bvar 1, .bvar 0]
    liftTermElabM do
      addAndCompile <| .defnDecl
        { name := n, levelParams := [], type := evalTy, value := nVal,
          hints := .abbrev, safety := .safe }
      addAndCompile <| .defnDecl
        { name := fast, levelParams := [], type := evalTy, value := fVal,
          hints := .abbrev, safety := .safe }
      -- @N = @N.fast, by guarded_eq (both sides unfold to it).
      let eqTy ← mkEq (mkConst n) (mkConst fast)
      let pf ← mkEqSymm (mkAppN (mkConst ``Certify.Refinement.guarded_eq)
        #[spec, cert, q, specEval, rConst])
      let pf ← mkExpectedTypeHint pf eqTy
      addDecl <| .thmDecl
        { name := n.str "eq_fast", levelParams := [], type := eqTy, value := pf }
    elabCommand (← `(attribute [csimp] $(mkIdent (n.str "eq_fast"))))
  | _ => throwUnsupportedSyntax

end Certify
