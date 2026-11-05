import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F8IndependentActualE2FullPhysicalGraphRebaseDE2
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F8IndependentE2UnconditionalPhysicalDomainDenseDC

/-!
BFSS M4F8 DE2B — PROSPECTIVE complete independent physical operator
domain equality and UNCONDITIONAL norm density, plus closedness.

The J-free actual E2 graph is rebased along BOTH the genuine
independent physical Hilbert input and 16-output subtype maps, as
defined by DE2. The representation witness J is used only to
discharge the exact original source-matching and analytical
hypotheses through accepted E7N2/DC theorems.

DE2 has not yet compiled or qualified. This file is uncompiled,
unaccepted, and must never be presented as an established result.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F8IndependentActualE2FullPhysicalDomainDE2B
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- The actual independent E2 graph is closed when BOTH input and
sixteen-component output are viewed as physical Hilbert subtypes.
This uses the literal original E2 IsClosed property, not a
new postulated closure. -/
theorem independentActualE2FullPhysicalChargeColumn_isClosed
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
      color gamma theta hCAR hHermitian).IsClosed := by
  change IsClosed
    ((FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
        color gamma theta hCAR hHermitian).graph :
      Set (independentPhysicalSpace theta hCAR hHermitian ×
        FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualPhysicalOutputs
          theta hCAR hHermitian))
  rw [FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn_graph_eq]
  change IsClosed
    {p : independentPhysicalSpace theta hCAR hHermitian ×
      FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualPhysicalOutputs
        theta hCAR hHermitian |
      ((p.1 : Lp E 2 μ), (p.2 : SpinIndex → Lp E 2 μ)) ∈
        (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
          color gamma theta hCAR hHermitian).graph}
  exact (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn_isClosed
    color gamma theta hCAR hHermitian J hColor hGamma hJ).preimage
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))

/-- Actual original E2 graph is the full rebased domain exactly:
physical input is already a subtype, and all 16 outputs remain
in the corresponding true independent physical submodule by E7N2. -/
theorem independentActualE2FullPhysicalChargeColumn_domain_iff
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w))
    (u : independentPhysicalSpace theta hCAR hHermitian) :
    u ∈
      (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
        color gamma theta hCAR hHermitian).domain ↔
      (u : Lp E 2 μ) ∈
        (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
          color gamma theta hCAR hHermitian).domain := by
  constructor
  · intro hu
    obtain ⟨y, hy⟩ := (LinearPMap.mem_domain_iff).mp hu
    have hp :
        ((u : Lp E 2 μ), (y : SpinIndex → Lp E 2 μ)) ∈
          (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
            color gamma theta hCAR hHermitian).graph := by
      have hrebased :
          (u, y) ∈
            FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalGraph
              color gamma theta hCAR hHermitian := by
        rw [← FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn_graph_eq]
        exact hy
      exact (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalGraph_mem_iff
        color gamma theta hCAR hHermitian (u, y)).mp hrebased
    exact (LinearPMap.mem_domain_iff).mpr
      ⟨(y : SpinIndex → Lp E 2 μ), hp⟩
  · intro hu
    obtain ⟨y, hy⟩ := (LinearPMap.mem_domain_iff).mp hu
    have hphysical :
        ∀ α : SpinIndex, y α ∈
          independentPhysicalSpace theta hCAR hHermitian :=
      (FCP.M4F7IndependentPhysicalOutputPredicateE7I.mem_independentAllSixteenOutputsPhysicalSet_iff
        theta hCAR hHermitian _).mp
          (FCP.M4F7IndependentActualClosedPhysicalOutputsE7N2.independentPhysicalInputCutClosedChargeColumn_graph_all_outputs_physical
            color gamma theta hCAR hHermitian J hColor hGamma hJ hy)
    have hyphysical :
        y ∈
          FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualPhysicalOutputs
            theta hCAR hHermitian := by
      change y ∈ Submodule.pi Set.univ
        (fun (_ : SpinIndex) => independentPhysicalSpace theta hCAR hHermitian)
      exact (Submodule.mem_pi).mpr (fun α _ => hphysical α)
    let v : FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualPhysicalOutputs
        theta hCAR hHermitian := ⟨y, hyphysical⟩
    apply (LinearPMap.mem_domain_iff).mpr
    refine ⟨v, ?_⟩
    rw [FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn_graph_eq]
    exact (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalGraph_mem_iff
      color gamma theta hCAR hHermitian (u, v)).mpr hy

/-- UNCONDITIONAL norm density of the actual fully J-free physical
16-charge column's domain, under original CAR/Hermitian and source
matching hypotheses, with the original source Haar premise discharged
by accepted DC Gate #1. This is not self-adjointness, graph-density or
physical Hamiltonian equality. -/
theorem independentActualE2FullPhysicalChargeColumn_domain_dense
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hColor : color = pairedAlgebraData.color)
    (hGamma : gamma = pairedAlgebraData.gamma)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    Dense ((FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
      color gamma theta hCAR hHermitian).domain :
        Set (independentPhysicalSpace theta hCAR hHermitian)) := by
  have hset :
      ((FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
        color gamma theta hCAR hHermitian).domain :
          Set (independentPhysicalSpace theta hCAR hHermitian)) =
      {u : independentPhysicalSpace theta hCAR hHermitian |
        (u : Lp E 2 μ) ∈
          (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
            color gamma theta hCAR hHermitian).domain} := by
    ext u
    exact independentActualE2FullPhysicalChargeColumn_domain_iff
      color gamma theta hCAR hHermitian J hColor hGamma hJ u
  rw [hset]
  exact FCP.M4F8IndependentE2UnconditionalPhysicalDomainDenseDC.independentE2_actual_closed_domain_dense_in_physical
    color gamma theta hCAR hHermitian J hColor hGamma hJ

#print axioms independentActualE2FullPhysicalChargeColumn_isClosed
#print axioms independentActualE2FullPhysicalChargeColumn_domain_iff
#print axioms independentActualE2FullPhysicalChargeColumn_domain_dense

end
end FCP.M4F8IndependentActualE2FullPhysicalDomainDE2B
