import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentFullSmoothCharge
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F1PairedSourceSpecialization

/-!
M4F1 — The original independent BFSS sixteen-charge family preserves
the INDEPENDENT gauge-invariant compactly supported smooth test core.

The independent charge and invariant core are both defined before and
without J. The proof uses the M4E5 exact original smooth-charge bridge,
the qualified original D3B source charge preservation theorem, and the
M4D1 independent-to-original invariant-core membership equivalence.

This is a theorem about the smooth invariant core. It does not claim
closed physical operators, graph closure, Hamiltonian equality, or
spectral conclusions.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentSmoothSupercharge
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentSmoothCore
open FCP.BFSSSU2PhysicalDomainD3B

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- Every independently defined BFSS supercharge preserves the
independent native-Spin gauge-invariant smooth-core submodule.
The given J is solely a WITNESS used to prove this J-free conclusion. -/
theorem independentCharge_mem_invariantCore
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (α : SpinIndex)
    (f : independentInvariantCore theta hCAR hHermitian) :
    independentCharge color gamma theta α f.val ∈
      independentInvariantCore theta hCAR hHermitian := by
  apply (independentInvariantCore_iff_source
    theta hCAR hHermitian J hJ
    (independentCharge color gamma theta α f.val)).2
  rw [independentCharge_intertwining color gamma theta J hColor hGamma hJ α f.val]
  let g : pairedGaugeData.invariantCore :=
    ⟨independentSmoothTransport J f.val,
      (independentInvariantCore_iff_source
        theta hCAR hHermitian J hJ f.val).1 f.prop⟩
  have hsource :
      pairedAlgebraData.charge α g.val ∈ pairedGaugeData.invariantCore :=
    FCP.BFSSM4F1SourceSpecialization.pairedOriginalCharge_mem_invariantCore α g
  have hg : g.val = independentSmoothTransport J f.val := rfl
  rw [hg] at hsource
  exact hsource

#print axioms independentCharge_mem_invariantCore
#check independentCharge_mem_invariantCore

end
end FCP.IndependentSmoothSupercharge
