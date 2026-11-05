import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AHOriginalSourceChargeParityConjugationProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AIOriginalFullL2ParityLiftProbe

/-!
# H5E8AM — exact sixteen-component original charge-vector parity

Source AH proved literal original supercharge parity on SmoothCore N.
Source AI proved the exact original coreToL2 embedding is compatible
with bosonic spatial parity in FullL2 N. Compose the two to obtain
parity covariance of ALL sixteen original source charge outputs,
without a surrogate BFSS charge model or hidden Hamiltonian equality.

The genuine physical invariant core and closed source graph are separate;
this lemma is a prerequisite for their later unitary transport and does
not assert the manuscript spectrum.
-/

set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AM
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AD
open FCP.BFSSSU2PhysicalDomainL6H5E8AF
open FCP.BFSSSU2PhysicalDomainL6H5E8AH
open FCP.BFSSSU2PhysicalDomainL6H5E8AI

/-- The previously accepted smooth-core parity is literally involutive
at each source test function. -/
theorem originalSmoothParity_twice {N : ℕ} (f : SmoothCore N) :
    originalSmoothParity (originalSmoothParity f) = f := by
  have h := congrArg
    (fun T : SmoothCore N →ₗ[ℂ] SmoothCore N => T f)
    (originalSmoothParity_involutive (N := N))
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h

/-- Exactly all source 16 charges obey the literal FullL2 parity
after transforming the input by the genuine smooth-core parity and
the source gamma data by the accepted oppositeGamma operation. -/
theorem originalChargeVector_parity {N : ℕ}
    (M : AlgebraData N) (f : SmoothCore N) :
    (oppositeGamma M).chargeVector (originalSmoothParity f) =
      (fun α : SpinIndex => originalFullL2Parity ((M.chargeVector f) α)) := by
  funext α
  change coreToL2
      ((oppositeGamma M).charge α (originalSmoothParity f)) =
    originalFullL2Parity (coreToL2 (M.charge α f))
  have h := congrArg
    (fun T : SmoothCore N →ₗ[ℂ] SmoothCore N =>
      T (originalSmoothParity f))
    (originalCharge_parityConjugate M α)
  change (oppositeGamma M).charge α (originalSmoothParity f) =
    originalSmoothParity
      (M.charge α (originalSmoothParity (originalSmoothParity f))) at h
  rw [originalSmoothParity_twice f] at h
  rw [h]
  exact (originalFullL2Parity_coreToL2 (M.charge α f)).symm

#print axioms originalSmoothParity_twice
#print axioms originalChargeVector_parity

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AM
