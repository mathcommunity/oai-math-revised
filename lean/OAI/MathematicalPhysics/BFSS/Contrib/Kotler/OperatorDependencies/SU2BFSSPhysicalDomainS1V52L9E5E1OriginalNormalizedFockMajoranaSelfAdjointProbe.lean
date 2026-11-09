import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5D1OriginalNativeSpin48FockCliffordAlgebraicCovarianceProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG1APairedThetaProbe
import Mathlib.Algebra.Star.SelfAdjoint

/-!
S1V52L9E5E1 — STAGED ONLY, UNQUALIFIED original normalized Fock
Majorana self-adjointness.

The original source pairedTheta operators have a source-accepted
self-adjointness theorem. The L9E2 Clifford-compatible Majorana
normalization multiplies precisely that same original operator by
the REAL POSITIVE sqrt(2), cast into ℂ. Since a real complex scalar
is self-adjoint, the actual normalized Fock operator is self-adjoint.

This is a distinct actual-Fock adjoint obligation needed before
studying Clifford even / native Spin(48) adjoint compatibility.
Do not infer the *odd* Clifford star is preserved by the Fock
representation: pinned CliffordAlgebra.star_ι = -ι, whereas the
Fock Majorana is self-adjoint. No Spin unitary or spectral claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000

namespace FCP.BFSSS1V52L9E5E1
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E2
open FCP.BFSSSU2GaugeG1A

/-- Exactly the actual original pairedTheta, normalized with real
positive sqrt(2), is self-adjoint on Fermion 2. -/
theorem originalNormalizedFockMajorana_selfAdjoint
    (α : RealSpinBlock) (A : Fin 3) :
    IsSelfAdjoint (originalNormalizedFockMajorana α A) := by
  change IsSelfAdjoint
    ((↑(Real.sqrt 2) : ℂ) • pairedTheta (spinPairEquiv.symm α) A)
  have hs : IsSelfAdjoint (↑(Real.sqrt 2) : ℂ) := by
    simp [isSelfAdjoint_iff]
  exact hs.smul (pairedTheta_selfAdjoint (spinPairEquiv.symm α) A)

#print axioms originalNormalizedFockMajorana_selfAdjoint

end
end FCP.BFSSS1V52L9E5E1
