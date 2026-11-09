import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentFullCoreGraphImage
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentFullL2Unitary

/-!
M4F5A — Explicit HOMEOMORPHISM on the unrestricted BFSS joint-charge
L² graph ambient space: one input plus the full sixteen-charge column.

Construction from M4C2's source-exact full-L² fiber unitary; inverse
is the actual fiber inverse. No new graph, gauge or physics hypotheses.
The topological equivalence is proved directly on Prod/Pi, not inferred
from an unbounded charge graph statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentSmoothSupercharge
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.IndependentFullL2GaugeTransport
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- The genuine 17-component homeomorphism induced by the accepted
full-L² isometric fiber equivalence. Its underlying map agrees with
the M4F4 graph image map, and the inverse is constructed explicitly. -/
def independentGraphTransportHomeomorph
    (J : E ≃ₗᵢ[ℂ] Fermion 2) :
    (Lp E 2 μ × (SpinIndex → Lp E 2 μ)) ≃ₜ
      (FullL2 2 × (SpinIndex → FullL2 2)) where
  toFun p :=
    (fiberTransport J p.1,
      fun α : SpinIndex => fiberTransport J (p.2 α))
  invFun q :=
    ((fiberTransportUnitary J).symm q.1,
      fun α : SpinIndex => (fiberTransportUnitary J).symm (q.2 α))
  left_inv := by
    intro p
    apply Prod.ext
    · exact (fiberTransportUnitary J).symm_apply_apply p.1
    · funext α
      exact (fiberTransportUnitary J).symm_apply_apply (p.2 α)
  right_inv := by
    intro q
    apply Prod.ext
    · exact (fiberTransportUnitary J).apply_symm_apply q.1
    · funext α
      exact (fiberTransportUnitary J).apply_symm_apply (q.2 α)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (fiberTransportUnitary J).continuous.comp continuous_fst
    · apply continuous_pi
      intro α
      exact (fiberTransportUnitary J).continuous.comp
        ((continuous_apply α).comp continuous_snd)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact (fiberTransportUnitary J).symm.continuous.comp continuous_fst
    · apply continuous_pi
      intro α
      exact (fiberTransportUnitary J).symm.continuous.comp
        ((continuous_apply α).comp continuous_snd)

#print axioms independentGraphTransportHomeomorph

end
end FCP.IndependentSmoothSupercharge
