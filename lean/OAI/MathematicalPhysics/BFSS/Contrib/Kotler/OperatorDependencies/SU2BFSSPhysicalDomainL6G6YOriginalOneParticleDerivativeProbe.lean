import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6XOriginalSU2GaugeCurveProbe

/-!
L6G6Y — derivative of the ORIGINAL complex 24-mode gauge matrix.

Use the accepted G3C block identity and the native SU(2) adjoint
derivative of X. The eight source color blocks have tangent f_(B A c),
and every off-block derivative vanishes. Recover the complete matrix
derivative by two applications of the pinned finite-Pi derivative law.

Boundary: this is the one-particle representation, not the exterior
Fock derivative, bounded fermionic generator equality, or Gauss theorem.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6Y
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG3A
open FCP.BFSSSU2GaugeG3C
open FCP.BFSSSU2PhysicalDomainL6G6U
open FCP.BFSSSU2PhysicalDomainL6G6X

/-- Actual source block derivative, with row B/output and column A/input. -/
theorem sourceComplexOneParticle_block_deriv
    (c : ColorIndex 2) (j k : Fin 8) (B A : ColorIndex 2) :
    HasDerivAt
      (fun t : ℝ => complexOneParticleMatrix (sourcePlusIGaugeCurve c t)
        (colorModeEquiv (j,B)) (colorModeEquiv (k,A)))
      (if j = k then (pairedAlgebraData.structureConstant B A c : ℂ) else 0) 0 := by
  by_cases h : j = k
  · have hd := (sourcePlusIGaugeCurve_adjointCoefficient_deriv c A B).ofReal_comp
    simpa only [complexOneParticleMatrix_block, _root_.ite_eq_left h, adjointColorMatrix] using hd
  · have hd : HasDerivAt (fun _ : ℝ => (0 : ℂ)) (0 : ℂ) (0 : ℝ) :=
      hasDerivAt_const (0 : ℝ) (0 : ℂ)
    simpa only [complexOneParticleMatrix_block, _root_.ite_eq_right h] using hd

/-- Every literal 24-mode matrix entry differentiates to the previously
computed candidate, which is now attached to the actual source group action. -/
theorem sourceComplexOneParticle_entry_deriv
    (c : ColorIndex 2) (m n : Fin 24) :
    HasDerivAt
      (fun t : ℝ => complexOneParticleMatrix (sourcePlusIGaugeCurve c t) m n)
      (source24ModeCandidateTangent c m n) 0 := by
  obtain ⟨⟨j,B⟩, rfl⟩ := colorModeEquiv.surjective m
  obtain ⟨⟨k,A⟩, rfl⟩ := colorModeEquiv.surjective n
  simpa only [source24ModeCandidateTangent_block] using
    sourceComplexOneParticle_block_deriv c j k B A

/-- The COMPLETE actual 24-by-24 one-particle gauge matrix derivative.
No one-particle or gauge-derivative premise is assumed. -/
theorem sourceComplexOneParticleMatrix_deriv
    (c : ColorIndex 2) :
    HasDerivAt
      (fun t : ℝ => complexOneParticleMatrix (sourcePlusIGaugeCurve c t))
      (source24ModeCandidateTangent c) 0 := by
  apply hasDerivAt_pi.mpr
  intro m
  apply hasDerivAt_pi.mpr
  intro n
  exact sourceComplexOneParticle_entry_deriv c m n

theorem sourceComplexOneParticleMatrix_zero (c : ColorIndex 2) :
    complexOneParticleMatrix (sourcePlusIGaugeCurve c 0) = 1 := by
  rw [sourcePlusIGaugeCurve_one, complexOneParticleMatrix_one]

#print axioms sourceComplexOneParticle_block_deriv
#print axioms sourceComplexOneParticle_entry_deriv
#print axioms sourceComplexOneParticleMatrix_deriv
#print axioms sourceComplexOneParticleMatrix_zero
#check @sourceComplexOneParticleMatrix_deriv

end
end FCP.BFSSSU2PhysicalDomainL6G6Y
