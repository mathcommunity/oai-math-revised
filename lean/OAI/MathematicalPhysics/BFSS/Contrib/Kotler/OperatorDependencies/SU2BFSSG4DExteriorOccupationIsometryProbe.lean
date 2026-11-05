import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4CFermionOperatorCovarianceProbe
import OAI.Analysis.Laughlin.Exterior.SpinUnitary

/-!
# BFSS SU(2) G4-D — true exterior Fock occupation-inner-product isometry

This adapts the pinned VectorAdjoint/SpinUnitary induction argument
to the actual, qualified BFSS SU(2) complexOneParticleMatrix acting
on all 24 Fock orbitals. The original upstream theorems concern a
different SourceSU2 representation and are NOT used as BFSS results.

G4-D proves inner product / mass invariance on the actual Space 23
exterior algebra. No exact Fermion 2 Hilbert unitary is claimed until
norm preservation is transported in a separate subsequent gate.
-/

namespace FCP.BFSSSU2GaugeG4D
noncomputable section

open scoped BigOperators Matrix
open Matrix
open OAI.BFSSQuantum
open OAI.Laughlin.Fock
open FCP.BFSSSU2GaugeG3C FCP.BFSSSU2GaugeG4A

/-- The dual orbital contraction is preserved by the actual
24×24 complex BFSS color-adjoint SU(2) unitary matrix. -/
theorem orbitalDual_gauge (g : GaugeGroup 2) (v : Orbital 23) :
    (orbitalDual 23 (orbitalGauge g v)).comp (orbitalGauge g) =
      orbitalDual 23 v := by
  apply LinearMap.ext
  intro w
  simp only [orbitalDual, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  change star (complexOneParticleMatrix g *ᵥ v) ⬝ᵥ
    (complexOneParticleMatrix g *ᵥ w) = star v ⬝ᵥ w
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, complexOneParticleMatrix_left_unitary,
    Matrix.vecMul_one]

/-- The *genuine* vector contraction intertwines the accepted BFSS
exterior gauge action, not the unrelated upstream SourceSU2 action. -/
theorem vectorAnnihilate_gauge (g : GaugeGroup 2)
    (v : Orbital 23) (x : Space 23) :
    vectorAnnihilate 23 (orbitalGauge g v) (exteriorGauge g x) =
      exteriorGauge g (vectorAnnihilate 23 v x) := by
  unfold vectorAnnihilate exteriorGauge
  rw [contraction_map, orbitalDual_gauge]

/-- The 24-mode exterior gauge action respects genuine wedge creation. -/
theorem exteriorGauge_ι_mul (g : GaugeGroup 2)
    (v : Orbital 23) (x : Space 23) :
    exteriorGauge g (ExteriorAlgebra.ι ℂ v * x) =
      ExteriorAlgebra.ι ℂ (orbitalGauge g v) * exteriorGauge g x := by
  simp [exteriorGauge]

/-- Scalar vacuum bras are invariant under the actual SU(2)
exterior gauge representation. -/
theorem occupationInner_scalar_gauge
    (g : GaugeGroup 2) (r : ℂ) (y : Space 23) :
    occupationInner 23 (algebraMap ℂ (Space 23) r) (exteriorGauge g y) =
      occupationInner 23 (algebraMap ℂ (Space 23) r) y := by
  induction y using CliffordAlgebra.left_induction with
  | algebraMap s => simp
  | add x y hx hy =>
      simp only [map_add, occupationInner_add_right, hx, hy]
  | ι_mul x v hx =>
      rw [exteriorGauge_ι_mul, occupationInner_scalar_wedge_zero,
        occupationInner_scalar_wedge_zero]

/-- Exact Fock occupation inner-product preservation for the entire
24-orbital exterior algebra, using the verified SU(2) unitary matrix. -/
theorem exteriorGauge_occupationInner
    (g : GaugeGroup 2) (x y : Space 23) :
    occupationInner 23 (exteriorGauge g x) (exteriorGauge g y) =
      occupationInner 23 x y := by
  revert y
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      intro y
      simp only [AlgHom.commutes]
      exact occupationInner_scalar_gauge g r y
  | add x z hx hz =>
      intro y
      simp only [map_add, occupationInner_add_left, hx, hz]
  | ι_mul x v hx =>
      intro y
      rw [exteriorGauge_ι_mul, vectorCreate_adjoint,
        vectorAnnihilate_gauge, hx, vectorCreate_adjoint]

/-- Occupation squared norm is unchanged under this actual BFSS
SU(2) gauge action, as a direct corollary of the full inner theorem. -/
theorem exteriorGauge_occupationNormSq (g : GaugeGroup 2) (x : Space 23) :
    occupationNormSq 23 (exteriorGauge g x) =
      occupationNormSq 23 x := by
  have h := exteriorGauge_occupationInner g x x
  rw [occupationInner_self, occupationInner_self] at h
  exact Complex.ofReal_injective h

#print axioms orbitalDual_gauge
#print axioms vectorAnnihilate_gauge
#print axioms exteriorGauge_ι_mul
#print axioms occupationInner_scalar_gauge
#print axioms exteriorGauge_occupationInner
#print axioms exteriorGauge_occupationNormSq

end
end FCP.BFSSSU2GaugeG4D
