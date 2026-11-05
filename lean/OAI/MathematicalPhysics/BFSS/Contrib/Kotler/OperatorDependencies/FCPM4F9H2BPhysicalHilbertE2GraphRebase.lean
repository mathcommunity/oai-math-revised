import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H2APhysicalHilbertOutputUnitary
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F8IndependentActualE2FullPhysicalGraphRebaseDE2

/-!
M4F9 H2B — FIRST Hilbert-output rebase for the ACTUAL independent E2 graph.

The accepted independent DE2 closed E2 sixteen-charge operator outputs in
Submodule.pi Set.univ inside SpinIndex → Lp E 2 μ. That finite function
space is normed by the ordinary function-space (sup) norm, not the
Hilbert PiLp 2 norm. Hilbert adjoints CANNOT be transported by treating
those norms as identical.

Construct explicitly a ℂ-linear coordinate inclusion from native
PiLp 2 of genuine independent physical Hilbert fibers into the already
accepted original DE2 sixteen-output subtype, then pull back the
EXISTING J-free actual E2 graph. Not a new charge or changed domain.

This stage proves only coordinate faithfulness and exact graph
membership. A closed, densely-defined LinearPMap into native Hilbert
outputs and its full domain/graph are subsequent tasks. No source
operator, Hamiltonian, or spectral conclusion is asserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H2BPhysicalHilbertE2GraphRebase
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
    theta α A * theta β B + theta β B * theta α A =
      (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)

/-- Exact coordinate embedding into the previously defined J-free
actual physical sixteen-output submodule, not a new output constraint. -/
noncomputable def hilbertPhysicalOutputsToActualOutputs :
    PiLp 2 (fun _ : SpinIndex =>
      independentPhysicalSpace theta hCAR hHermitian) →ₗ[ℂ]
    FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualPhysicalOutputs
      theta hCAR hHermitian where
  toFun v :=
    ⟨(fun α => ((v α : independentPhysicalSpace theta hCAR hHermitian) :
          Lp E 2 μ)), by
      change (fun α => ((v α : independentPhysicalSpace theta hCAR hHermitian) :
        Lp E 2 μ)) ∈
        Submodule.pi Set.univ
          (fun (_ : SpinIndex) => independentPhysicalSpace theta hCAR hHermitian)
      exact (Submodule.mem_pi).mpr (fun α _ => (v α).property)⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    funext α
    rfl
  map_smul' := by
    intro c a
    apply Subtype.ext
    funext α
    rfl

/-- Hilbert-output coordinates are literally the original gauge-physical
sixteen functions under the canonical subtype coercions. -/
theorem hilbertPhysicalOutputsToActualOutputs_apply
    (v : PiLp 2 (fun _ : SpinIndex =>
      independentPhysicalSpace theta hCAR hHermitian))
    (α : SpinIndex) :
    ((hilbertPhysicalOutputsToActualOutputs theta hCAR hHermitian v :
      SpinIndex → Lp E 2 μ) α) = (v α : Lp E 2 μ) := by
  rfl

/-- No information in the sixteen physical fiber coordinates is lost
by Hilbert rebasing; essential for vertical single-valuedness later. -/
theorem hilbertPhysicalOutputsToActualOutputs_injective :
    Function.Injective
      (hilbertPhysicalOutputsToActualOutputs theta hCAR hHermitian) := by
  intro a b hab
  apply PiLp.ext
  intro α
  apply Subtype.ext
  exact congrArg
    (fun w : FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualPhysicalOutputs
      theta hCAR hHermitian =>
        (w : SpinIndex → Lp E 2 μ) α) hab

/-- Pull back the genuinely independent DE2 E2 graph into its NATIVE
sixteen-output PiLp 2 Hilbert coordinate space. No independent
charge operator is replaced, extended or redefined here. -/
noncomputable def independentActualE2HilbertPhysicalGraph
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix) :
    Submodule ℂ
      (independentPhysicalSpace theta hCAR hHermitian ×
        PiLp 2 (fun _ : SpinIndex =>
          independentPhysicalSpace theta hCAR hHermitian)) :=
  (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
    color gamma theta hCAR hHermitian).graph.comap
    ((LinearMap.id : independentPhysicalSpace theta hCAR hHermitian →ₗ[ℂ]
      independentPhysicalSpace theta hCAR hHermitian).prodMap
        (hilbertPhysicalOutputsToActualOutputs theta hCAR hHermitian))

/-- Literal iff for membership in the ACTUAL J-free DE2 graph after
native Hilbert output-coordinate rebasing. -/
theorem independentActualE2HilbertPhysicalGraph_mem_iff
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (p : independentPhysicalSpace theta hCAR hHermitian ×
      PiLp 2 (fun _ : SpinIndex =>
        independentPhysicalSpace theta hCAR hHermitian)) :
    p ∈ independentActualE2HilbertPhysicalGraph
      theta hCAR hHermitian color gamma ↔
    (p.1, hilbertPhysicalOutputsToActualOutputs theta hCAR hHermitian p.2) ∈
      (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
        color gamma theta hCAR hHermitian).graph := by
  rfl

#print axioms hilbertPhysicalOutputsToActualOutputs
#print axioms hilbertPhysicalOutputsToActualOutputs_apply
#print axioms hilbertPhysicalOutputsToActualOutputs_injective
#print axioms independentActualE2HilbertPhysicalGraph
#print axioms independentActualE2HilbertPhysicalGraph_mem_iff

end
end FCP.M4F9H2BPhysicalHilbertE2GraphRebase
