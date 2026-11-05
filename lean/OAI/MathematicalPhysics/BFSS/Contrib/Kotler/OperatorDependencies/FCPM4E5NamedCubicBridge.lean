import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4E5RawSourceCertificates

/-!
M4E5 diagnostic D: independent cubic-to-NAMED source operator
transport, isolated from kinetic and full charge.

Use the STRICTLY ACCEPTED M4E4B cubic proof. The named source
operator is the literal second finite sum in pinned AlgebraData.charge.
No changes to coefficients, source identity, hypotheses or physics.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.IndependentSmoothSupercharge
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.IndependentSmoothCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- The already accepted cubic source bridge, packaged behind
the separately verified originalSourceCubicPart interface. -/
theorem independentCubic_named_source_intertwining
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (α : SpinIndex) (f : IndependentTestCore E) :
    independentSmoothTransport J (independentCubicCharge color gamma theta α f) =
      originalSourceCubicPart pairedAlgebraData α
        (independentSmoothTransport J f) := by
  exact (independentCubicCharge_intertwining
    color gamma theta J hColor hGamma hJ α f).trans
    (congrArg
      (fun T : SmoothCore 2 →ₗ[ℂ] SmoothCore 2 =>
        T (independentSmoothTransport J f))
      (originalSourceCubicPart_eq_sum pairedAlgebraData α).symm)

#print axioms independentCubic_named_source_intertwining

end
end FCP.IndependentSmoothSupercharge
