import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8ASOriginalPhysicalClosedChargeGraphEnergyParityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AJOriginalFullL2ParityUnitaryProbe
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# H5E8AT — genuine source sixteen-charge Hilbert PiLp 2 parity UNITARY

The accepted AJ original FullL2 spatial parity is a genuine
complex-linear isometry equivalence. The pinned Mathlib's
LinearIsometryEquiv.piLpCongrRight 2 constructs the canonical
sixteen-component Hilbert direct-sum unitary, the actual output
ambient required by the accepted D2B17 original-source adjoint.

AS already qualified exact 1/16 squared-norm scalar preservation on
the original closed gauge-restricted sixteen-charge graph. This probe
certifies that its componentwise parity is also an actual unitary
on the correct PiLp 2 Hilbert output, not merely an ℓ∞ product map.
Still not the distinct manuscript Clifford realization, associated
unbounded Hamiltonian domain, or a spectral claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AT
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2PhysicalDomainL6H5E8AI
open FCP.BFSSSU2PhysicalDomainL6H5E8AJ
open FCP.BFSSSU2PhysicalDomainL6H5E8AS
open scoped InnerProductSpace

/-- The ACTUAL original source sixteen-component L² Hilbert direct
sum is preserved by simultaneous original FullL2 parity. -/
noncomputable def originalChargeHilbertOutputParityUnitary {N : ℕ} :
    PiLp 2 (fun _ : SpinIndex => FullL2 N) ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : SpinIndex => FullL2 N) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun _ : SpinIndex => originalFullL2ParityUnitary (N := N))

/-- All actual sixteen Hilbert output components transform by the
original source-genuine FullL2 parity, with no surrogate spin index. -/
theorem originalChargeHilbertOutputParityUnitary_apply {N : ℕ}
    (y : PiLp 2 (fun _ : SpinIndex => FullL2 N))
    (α : SpinIndex) :
    originalChargeHilbertOutputParityUnitary y α =
      originalFullL2Parity (y α) := by
  rfl

/-- This original sixteen-output map is genuinely Hilbert-isometric,
not merely continuous or equivalent in the product topology. -/
theorem originalChargeHilbertOutputParityUnitary_norm {N : ℕ}
    (y : PiLp 2 (fun _ : SpinIndex => FullL2 N)) :
    ‖originalChargeHilbertOutputParityUnitary y‖ = ‖y‖ := by
  exact (originalChargeHilbertOutputParityUnitary (N := N)).norm_map y

/-- Parity is an involution on the whole actual Hilbert direct sum. -/
theorem originalChargeHilbertOutputParityUnitary_twice {N : ℕ}
    (y : PiLp 2 (fun _ : SpinIndex => FullL2 N)) :
    originalChargeHilbertOutputParityUnitary
      (originalChargeHilbertOutputParityUnitary y) = y := by
  apply PiLp.ext
  intro α
  change originalFullL2Parity (originalFullL2Parity (y α)) = y α
  exact originalFullL2Parity_involutive (y α)

/-- Exact source 1/16 finite output expression is the same after
the genuinely Hilbert-valued unitary, not merely after product parity. -/
theorem originalChargeHilbertOutputEnergy_parity {N : ℕ}
    (y : PiLp 2 (fun _ : SpinIndex => FullL2 N)) :
    originalChargeOutputEnergy
      (fun α => originalChargeHilbertOutputParityUnitary y α) =
    originalChargeOutputEnergy (fun α => y α) := by
  have he := originalChargeOutputEnergy_parity
    (fun α : SpinIndex => y α)
  simpa only [originalChargeHilbertOutputParityUnitary_apply] using he

#print axioms originalChargeHilbertOutputParityUnitary
#print axioms originalChargeHilbertOutputParityUnitary_apply
#print axioms originalChargeHilbertOutputParityUnitary_norm
#print axioms originalChargeHilbertOutputParityUnitary_twice
#print axioms originalChargeHilbertOutputEnergy_parity

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AT
