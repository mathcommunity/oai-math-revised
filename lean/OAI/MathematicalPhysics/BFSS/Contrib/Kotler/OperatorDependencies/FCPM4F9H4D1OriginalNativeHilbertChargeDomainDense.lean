import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H4C2DExactNativeChargeAction

/-!
BFSS M4F9 H4D1 — ACTUAL ORIGINAL AY native sixteen-output Hilbert
charge has unconditionally dense natural domain. Transfer density by
the accepted H3B2 exact NATIVE/AMBIENT source charge-domain iff,
using the ORIGINAL source Haar-core closure theorem BA.

No fabricated native source core and no adjoint/Hamiltonian equality.
The independent native density is already accepted H2D2A and is
distinct; both dense domains are prerequisites for proper adjoints.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H4D1OriginalNativeHilbertChargeDomainDense
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.M4F9H3B2OriginalAYNativePhysicalHilbertChargeColumn
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)
variable (color : ColorIndex 2 → ColorMatrix 2)
variable (gamma : SpaceIndex → GammaMatrix)
variable (J : E ≃ₗᵢ[ℂ] Fermion 2)
variable (hColor : color = pairedAlgebraData.color)
variable (hGamma : gamma = pairedAlgebraData.gamma)
variable (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
include theta hCAR hHermitian color gamma J hColor hGamma hJ

/-- Exact entire native original AY sixteen-output source Hilbert
charge natural domain is dense, using the original source Haar proof;
no assumed density and no replacement source charge. -/
theorem pairedOriginalNativePhysicalHilbertChargeColumn_domain_dense :
    Dense ((pairedOriginalNativePhysicalHilbertChargeColumn.domain :
      Set pairedGaugeData.physicalSpace)) := by
  have hdom :
      pairedOriginalNativePhysicalHilbertChargeColumn.domain =
        (originalMinimalPhysicalHilbertChargeColumn
          pairedAlgebraData pairedGaugeData).domain := by
    ext u
    exact pairedOriginalNativePhysicalHilbertChargeColumn_domain_iff
      theta hCAR hHermitian color gamma J hColor hGamma hJ u
  rw [hdom]
  exact FCP.BFSSSU2PhysicalDomainL6H5E8BA.originalMinimalPhysicalHilbertChargeColumn_domain_dense_unconditional
    pairedAlgebraData pairedGaugeData

#print axioms pairedOriginalNativePhysicalHilbertChargeColumn_domain_dense
end
end FCP.M4F9H4D1OriginalNativeHilbertChargeDomainDense
