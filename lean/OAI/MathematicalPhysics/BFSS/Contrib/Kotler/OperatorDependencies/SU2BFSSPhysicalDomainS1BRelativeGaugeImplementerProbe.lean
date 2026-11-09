import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1ASchurScalarCommutantProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4HExactThetaCovarianceProbe

/-!
# BFSS SU(2) S1B — uniqueness up to scalar of exact theta-covariant gauge implementers

S1A proves the scalar commutant of the literal 48 Majoranas on Fermion 2.
Here an arbitrary invertible complex-linear candidate implementing the SAME
48-generator color covariance as FCP's accepted fermionic SU(2) action must
equal that exact action up to one complex scalar.

Crucial conditionality: the candidate covariance is an explicit hypothesis.
This theorem does not manufacture the manuscript's Spin(48) lift, establish a
global SU(2) character, or prove manuscript Hamiltonian/spectral identity.
-/

namespace FCP.BFSSSU2PhysicalDomainS1B
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2GaugeG4E
open FCP.BFSSSU2GaugeG4H
open FCP.BFSSSU2PhysicalDomainS1A

/-- Any same-covariance implementer of the literal source theta family
is the accepted exterior-Fock gauge action times a single scalar.
The candidate's existence and covariance are assumptions, not conclusions. -/
theorem theta_covariant_implementer_scalar
    (g : GaugeGroup 2) (V : Fermion 2 ≃ₗ[ℂ] Fermion 2)
    (hV : ∀ (α : SpinIndex) (A : ColorIndex 2) (v : Fermion 2),
      V (pairedTheta α A v) =
        ∑ B : ColorIndex 2,
          (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
            pairedTheta α B (V v)) :
    ∃ z : ℂ, ∀ v : Fermion 2,
      V v = z • fermionGaugeLinearEquiv g v := by
  let F : Fermion 2 ≃ₗ[ℂ] Fermion 2 := fermionGaugeLinearEquiv g
  let L : Module.End ℂ (Fermion 2) := F.symm.toLinearMap.comp V.toLinearMap
  have hcomm : ∀ (α : SpinIndex) (A : ColorIndex 2) (v : Fermion 2),
      L (pairedTheta α A v) = pairedTheta α A (L v) := by
    intro α A v
    change F.symm (V (pairedTheta α A v)) =
      pairedTheta α A (F.symm (V v))
    apply F.injective
    rw [LinearEquiv.apply_symm_apply]
    rw [hV α A v]
    have hF := pairedAlgebraData_fermion_adjoint g α A (F.symm (V v))
    change F (pairedTheta α A (F.symm (V v))) =
      ∑ B : ColorIndex 2,
        (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
          pairedTheta α B (F (F.symm (V v))) at hF
    rw [hF]
    simp only [LinearEquiv.apply_symm_apply]
  obtain ⟨z, hz⟩ := pairedTheta_commutant_scalar L hcomm
  refine ⟨z, ?_⟩
  intro v
  have hv := hz v
  change F.symm (V v) = z • v at hv
  have hmap := congrArg (fun w : Fermion 2 => F w) hv
  simpa only [LinearEquiv.apply_symm_apply, map_smul] using hmap

#print axioms theta_covariant_implementer_scalar

end
end FCP.BFSSSU2PhysicalDomainS1B
