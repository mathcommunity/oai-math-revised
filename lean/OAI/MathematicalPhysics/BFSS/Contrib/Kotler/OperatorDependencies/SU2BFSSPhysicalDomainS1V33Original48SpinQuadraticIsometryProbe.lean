import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V32AllSpin48CanonicalVectorLinearGroupActionProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
S1V33 — original source-sized Spin48 quadratic preservation via the
REAL Clifford algebra, not an assumed SO48 action.

The accepted S1V31–32 theorem sequence gives arbitrary Spin48 source
real-vector conjugation, additive/real-scalar and group action laws.
Here we prove the real Clifford scalar embedding injective by the exact
Mathlib Clifford-to-exterior equivalence (whose exterior scalar map has
a genuine left inverse), then apply the Clifford square relation.

IMPORTANT: The algebraMap into Clifford is NOT universally injective
over arbitrary base rings (cf pinned Mathlib counterexample); we claim
only the actual ℝ Clifford algebra on Fin24 × Fin2 with source Q.

NEW UNCOMPILED CANDIDATE until immutable strict CI. No Q-preserving
SO group hom, det +1, Spin double cover, global SU2 lift or BFSS gap
is claimed by this file before independent kernel acceptance.
-/

set_option autoImplicit false
set_option maxHeartbeats 330000

namespace FCP.BFSSS1V33
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V31

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- The scalar embedding of the EXACT REAL SOURCE Clifford algebra is
injective, using pinned Mathlib's field/2-invertible exterior model.
This is not a claim about Clifford algebras over general rings. -/
theorem source48_real_clifford_scalar_injective :
    Function.Injective (algebraMap ℝ C) := by
  intro a b hab
  apply (ExteriorAlgebra.algebraMap_leftInverse Source48Vector).injective
  have hExterior := congrArg (CliffordAlgebra.equivExterior Q) hab
  simpa only [CliffordAlgebra.equivExterior,
    CliffordAlgebra.changeFormEquiv_apply,
    CliffordAlgebra.changeForm_algebraMap] using hExterior

/-- Clifford conjugation by ANY genuine source Spin48 element fixes
the real scalar embedding, exactly (not merely up to a scalar phase). -/
theorem source48_spin_conjugation_fixes_real_scalar
    (s : spinGroup Q) (a : ℝ) :
    ConjAct.toConjAct (spinGroup.toUnits s) •
      (algebraMap ℝ C a) = algebraMap ℝ C a := by
  let u : Cˣ := spinGroup.toUnits s
  change (u : C) * algebraMap ℝ C a * ((u⁻¹ : Cˣ) : C) =
    algebraMap ℝ C a
  calc
    (u : C) * algebraMap ℝ C a * ((u⁻¹ : Cˣ) : C) =
        algebraMap ℝ C a * ((u : C) * ((u⁻¹ : Cˣ) : C)) := by
      rw [← (Algebra.commutes a (u : C)), mul_assoc]
    _ = algebraMap ℝ C a := by simp

/-- For EVERY genuine Spin48 element and EVERY original source vector,
its canonical real action preserves the actual source quadratic form,
transporting the Clifford square relation through conjugation and
using source-specific real scalar injectivity. -/
theorem sourceSpin48VectorAction_preserves_sourceQ
    (s : spinGroup Q) (v : Source48Vector) :
    Q (sourceSpin48VectorAction s v) = Q v := by
  apply source48_real_clifford_scalar_injective
  calc
    algebraMap ℝ C (Q (sourceSpin48VectorAction s v)) =
        (CliffordAlgebra.ι Q (sourceSpin48VectorAction s v)) *
          (CliffordAlgebra.ι Q (sourceSpin48VectorAction s v)) :=
      (CliffordAlgebra.ι_sq_scalar Q _).symm
    _ =
        (ConjAct.toConjAct (spinGroup.toUnits s) • (CliffordAlgebra.ι Q v)) *
          (ConjAct.toConjAct (spinGroup.toUnits s) • (CliffordAlgebra.ι Q v)) := by
      rw [sourceSpin48VectorAction_clifford_generator]
    _ =
        ConjAct.toConjAct (spinGroup.toUnits s) •
          (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v) := by
      rw [smul_mul']
    _ =
        ConjAct.toConjAct (spinGroup.toUnits s) •
          algebraMap ℝ C (Q v) := by
      rw [CliffordAlgebra.ι_sq_scalar]
    _ = algebraMap ℝ C (Q v) :=
      source48_spin_conjugation_fixes_real_scalar s (Q v)

#print axioms source48_real_clifford_scalar_injective
#print axioms source48_spin_conjugation_fixes_real_scalar
#print axioms sourceSpin48VectorAction_preserves_sourceQ

end
end FCP.BFSSS1V33
