import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H2BPhysicalHilbertE2GraphRebase

/-! H2C: Actual independently defined E2 operator graph on a genuine
PiLp 2 physical Hilbert codomain. Proves verticality via the previously
qualified DE2 charge and H2B injective coordinate map. No source-defined
replacement charge and no Hamiltonian or spectral conclusion. -/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H2CActualE2NativeHilbertChargeColumn
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.M4F9H2BPhysicalHilbertE2GraphRebase
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

theorem independentActualE2HilbertPhysicalGraph_vertical :
    ∀ p : independentPhysicalSpace theta hCAR hHermitian ×
      PiLp 2 (fun _ : SpinIndex =>
        independentPhysicalSpace theta hCAR hHermitian),
      p ∈ independentActualE2HilbertPhysicalGraph
        theta hCAR hHermitian color gamma →
      p.1 = 0 → p.2 = 0 := by
  rintro ⟨u, y⟩ hp hu
  dsimp at hu
  subst u
  have hactual :
      ((0 : independentPhysicalSpace theta hCAR hHermitian),
        hilbertPhysicalOutputsToActualOutputs theta hCAR hHermitian y) ∈
      (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
        color gamma theta hCAR hHermitian).graph :=
    (independentActualE2HilbertPhysicalGraph_mem_iff
      theta hCAR hHermitian color gamma (0, y)).mp hp
  have hzero :
      hilbertPhysicalOutputsToActualOutputs theta hCAR hHermitian y = 0 :=
    (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
      color gamma theta hCAR hHermitian).graph_fst_eq_zero_snd hactual rfl
  apply hilbertPhysicalOutputsToActualOutputs_injective theta hCAR hHermitian
  simpa only [map_zero] using hzero

noncomputable def independentActualE2NativeHilbertChargeColumn :
    independentPhysicalSpace theta hCAR hHermitian →ₗ.[ℂ]
      PiLp 2 (fun _ : SpinIndex =>
        independentPhysicalSpace theta hCAR hHermitian) :=
  (independentActualE2HilbertPhysicalGraph
    theta hCAR hHermitian color gamma).toLinearPMap

theorem independentActualE2NativeHilbertChargeColumn_graph_eq :
    (independentActualE2NativeHilbertChargeColumn
      theta hCAR hHermitian color gamma).graph =
    independentActualE2HilbertPhysicalGraph
      theta hCAR hHermitian color gamma := by
  exact Submodule.toLinearPMap_graph_eq _
    (independentActualE2HilbertPhysicalGraph_vertical
      theta hCAR hHermitian color gamma)

#print axioms independentActualE2HilbertPhysicalGraph_vertical
#print axioms independentActualE2NativeHilbertChargeColumn
#print axioms independentActualE2NativeHilbertChargeColumn_graph_eq

end
end FCP.M4F9H2CActualE2NativeHilbertChargeColumn
