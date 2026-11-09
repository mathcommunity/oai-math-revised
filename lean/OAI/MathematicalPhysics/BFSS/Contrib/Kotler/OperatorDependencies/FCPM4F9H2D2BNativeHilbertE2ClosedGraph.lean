import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H2D2ANativeHilbertE2ContinuityAndDensity

/-!
BFSS M4F9 H2D2B — CLOSED actual independent E2 partial charge column
with TRUE physical Hilbert PiLp 2 output and natural input domain.

Native graph is the original DE2 closed E2 graph comapped along the
identity on independent physical input and H2D2A's independently
proved continuous Hilbert-to-actual physical 16-output coordinate map.
No identification of sup and PiLp2 norms, no different charge or
unjustified source/Hamiltonian equivalence.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H2D2BNativeHilbertE2ClosedGraph
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.M4F9H2BPhysicalHilbertE2GraphRebase
open FCP.M4F9H2CActualE2NativeHilbertChargeColumn
open FCP.M4F9H2D2ANativeHilbertE2ContinuityAndDensity
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

/-- The literal native independent actual E2 sixteen-charge partial
operator is CLOSED in the TRUE Hilbert-product graph topology.
Source-matching hypotheses enter only through the accepted E2B
closedness theorem, and do not define the J-free E2 operator. -/
theorem independentActualE2NativeHilbertChargeColumn_isClosed
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    (independentActualE2NativeHilbertChargeColumn
      theta hCAR hHermitian color gamma).IsClosed := by
  change IsClosed
    ((independentActualE2NativeHilbertChargeColumn
      theta hCAR hHermitian color gamma).graph :
        Set (independentPhysicalSpace theta hCAR hHermitian ×
          PiLp 2 (fun _ : SpinIndex =>
            independentPhysicalSpace theta hCAR hHermitian)))
  rw [independentActualE2NativeHilbertChargeColumn_graph_eq]
  change IsClosed
    {p : independentPhysicalSpace theta hCAR hHermitian ×
      PiLp 2 (fun _ : SpinIndex =>
        independentPhysicalSpace theta hCAR hHermitian) |
      (p.1, hilbertPhysicalOutputsToActualOutputs theta hCAR hHermitian p.2) ∈
        (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
          color gamma theta hCAR hHermitian).graph}
  exact
    (FCP.M4F8IndependentActualE2FullPhysicalDomainDE2B.independentActualE2FullPhysicalChargeColumn_isClosed
      color gamma theta hCAR hHermitian J hColor hGamma hJ).preimage
      (continuous_fst.prodMk
        ((hilbertPhysicalOutputsToActualOutputs_continuous
          theta hCAR hHermitian).comp continuous_snd))

#print axioms independentActualE2NativeHilbertChargeColumn_isClosed

end
end FCP.M4F9H2D2BNativeHilbertE2ClosedGraph
