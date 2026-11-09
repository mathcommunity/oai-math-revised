import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4E5RawSourceCertificates

/-!
M4E5 diagnostic C: independent kinetic-to-NAMED source operator
transport, isolated from the cubic transport and full charge.

Use the STRICTLY ACCEPTED M4E3 kinetic proof. The named source
operator is the literal first finite sum in pinned AlgebraData.charge.
No new kinetic term, no J-dependent independent definition, and no
full charge source unfolding is introduced.
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

/-- The already accepted kinetic source bridge, packaged behind
the separately verified originalSourceKineticPart interface. -/
theorem independentKinetic_named_source_intertwining
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (α : SpinIndex) (f : IndependentTestCore E) :
    independentSmoothTransport J (independentKineticCharge gamma theta α f) =
      originalSourceKineticPart pairedAlgebraData α
        (independentSmoothTransport J f) := by
  exact (independentKineticCharge_intertwining
    gamma theta J hGamma hJ α f).trans
    (congrArg
      (fun T : SmoothCore 2 →ₗ[ℂ] SmoothCore 2 =>
        T (independentSmoothTransport J f))
      (originalSourceKineticPart_eq_sum pairedAlgebraData α).symm)

#print axioms independentKinetic_named_source_intertwining

end
end FCP.IndependentSmoothSupercharge
