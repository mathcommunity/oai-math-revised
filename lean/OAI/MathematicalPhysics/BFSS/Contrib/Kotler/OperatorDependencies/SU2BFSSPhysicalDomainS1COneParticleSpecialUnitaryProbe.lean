import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG3CComplexOneParticleUnitaryProbe
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# BFSS SU(2) S1C — determinant-one exact 24-mode one-particle action

The accepted oneParticleMatrix g is eight identical real orthogonal
three-color blocks, reindexed by the exact 8 x 3 -> 24 Fock mode map.
Consequently its determinant is one, even using only orthogonality
of the color block (whose determinant is ±1). Complex scalar extension
remains determinant one, so the actual accepted one-particle SU(2)
representation lands in SU(24), not merely U(24).

This removes a determinant/phase obstruction on the route to identifying
the second-quantized action with a Spin(48) lift. It does NOT itself
construct that lift or identify the manuscript Hamiltonian.
-/

namespace FCP.BFSSSU2PhysicalDomainS1C
noncomputable section

open scoped Kronecker
open Matrix
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG3A
open FCP.BFSSSU2GaugeG3B
open FCP.BFSSSU2GaugeG3C
open OAI.BFSSQuantum

theorem adjointColorMatrix_det_sq_one (g : GaugeGroup 2) :
    (adjointColorMatrix g).det ^ 2 = 1 := by
  have h := congrArg Matrix.det (adjointColorMatrix_orthogonal g)
  simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, pow_two] using h

theorem oneParticleMatrix_det_one (g : GaugeGroup 2) :
    (oneParticleMatrix g).det = 1 := by
  have hsq := adjointColorMatrix_det_sq_one g
  calc
    (oneParticleMatrix g).det = (colorBlocks g).det := by
      change Matrix.det (Matrix.reindexAlgEquiv ℝ ℝ colorModeEquiv (colorBlocks g)) = _
      exact Matrix.det_reindexAlgEquiv ℝ ℝ colorModeEquiv (colorBlocks g)
    _ = (adjointColorMatrix g).det ^ 8 := by
      change ((1 : Matrix (Fin 8) (Fin 8) ℝ) ⊗ₖ adjointColorMatrix g).det =
        (adjointColorMatrix g).det ^ 8
      rw [Matrix.det_kronecker]
      simp
    _ = ((adjointColorMatrix g).det ^ 2) ^ 4 := by ring
    _ = 1 := by rw [hsq]; norm_num

/-- The literal 24 x 24 complex source one-particle action has determinant one. -/
theorem complexOneParticleMatrix_det_one (g : GaugeGroup 2) :
    (complexOneParticleMatrix g).det = 1 := by
  change Matrix.det ((algebraMap ℝ ℂ).mapMatrix (oneParticleMatrix g)) = 1
  rw [← (algebraMap ℝ ℂ).map_det]
  rw [oneParticleMatrix_det_one]
  simp

/-- The actual 24-mode BFSS matrix, now inhabiting the exact SU(24) subtype. -/
noncomputable def complexOneParticleSpecialUnitary (g : GaugeGroup 2) :
    Matrix.specialUnitaryGroup (Fin 24) ℂ := by
  refine ⟨complexOneParticleMatrix g, ?_⟩
  rw [Matrix.mem_specialUnitaryGroup_iff]
  exact ⟨(complexOneParticleUnitary g).property, complexOneParticleMatrix_det_one g⟩

/-- Exact source-defined SU(2) representation into SU(24), not only U(24). -/
noncomputable def complexOneParticleSpecialUnitaryHom :
    GaugeGroup 2 →* Matrix.specialUnitaryGroup (Fin 24) ℂ where
  toFun := complexOneParticleSpecialUnitary
  map_one' := by
    apply Subtype.ext
    change complexOneParticleMatrix 1 = 1
    exact complexOneParticleMatrix_one
  map_mul' g h := by
    apply Subtype.ext
    change complexOneParticleMatrix (g * h) =
      complexOneParticleMatrix g * complexOneParticleMatrix h
    exact complexOneParticleMatrix_mul g h

#print axioms adjointColorMatrix_det_sq_one
#print axioms oneParticleMatrix_det_one
#print axioms complexOneParticleMatrix_det_one
#print axioms complexOneParticleSpecialUnitary
#print axioms complexOneParticleSpecialUnitaryHom

end
end FCP.BFSSSU2PhysicalDomainS1C
