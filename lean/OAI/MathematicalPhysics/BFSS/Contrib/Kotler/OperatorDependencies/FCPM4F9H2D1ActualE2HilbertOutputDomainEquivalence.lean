import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F9H2CActualE2NativeHilbertChargeColumn

/-!
BFSS M4F9 H2D1: true native PiLp2 physical output coordinates cover the
ENTIRE existing independent DE2 physical output submodule, because the
spin index is finite and PiLp 2 is a WithLp model of the full Pi type.

This permits the EXACT NATURAL DOMAIN of the newly accepted native
physical Hilbert charge to be identified with the ALREADY accepted
independent DE2 physical charge. No source/J-defined replacement,
domain extension, adjoint or Hamiltonian claims.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F9H2D1ActualE2HilbertOutputDomainEquivalence
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.M4F9H2BPhysicalHilbertE2GraphRebase
open FCP.M4F9H2CActualE2NativeHilbertChargeColumn
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))
variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)
variable (color : ColorIndex 2 → ColorMatrix 2)
variable (gamma : SpaceIndex → GammaMatrix)

/-- The H2B coordinate map is onto the *actual* DE2 16-physical-output
submodule, not only injective; use original membership, no new output. -/
theorem hilbertPhysicalOutputsToActualOutputs_surjective :
    Function.Surjective
      (hilbertPhysicalOutputsToActualOutputs theta hCAR hHermitian) := by
  intro y
  have hy :
      (y : SpinIndex → Lp E 2 μ) ∈
        Submodule.pi Set.univ
          (fun (_ : SpinIndex) =>
            independentPhysicalSpace theta hCAR hHermitian) :=
    y.property
  have hcoords (α : SpinIndex) :
      (y : SpinIndex → Lp E 2 μ) α ∈
        independentPhysicalSpace theta hCAR hHermitian :=
    (Submodule.mem_pi).mp hy α (Set.mem_univ α)
  refine ⟨WithLp.toLp 2 (fun α : SpinIndex =>
      (⟨(y : SpinIndex → Lp E 2 μ) α, hcoords α⟩ :
        independentPhysicalSpace theta hCAR hHermitian)), ?_⟩
  apply Subtype.ext
  funext α
  rfl

/-- Full EXACT natural domain of the native PiLp2 Hilbert E2 partial
operator equals the existing J-free DE2 independent physical E2 domain.
This uses actual graph iff, not an assumption about source operators. -/
theorem independentActualE2NativeHilbertChargeColumn_domain_iff
    (u : independentPhysicalSpace theta hCAR hHermitian) :
    u ∈ (independentActualE2NativeHilbertChargeColumn
      theta hCAR hHermitian color gamma).domain ↔
    u ∈ (FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2.independentActualE2FullPhysicalChargeColumn
      color gamma theta hCAR hHermitian).domain := by
  constructor
  · intro hu
    obtain ⟨v, hv⟩ := (LinearPMap.mem_domain_iff).mp hu
    rw [independentActualE2NativeHilbertChargeColumn_graph_eq] at hv
    exact (LinearPMap.mem_domain_iff).mpr
      ⟨hilbertPhysicalOutputsToActualOutputs theta hCAR hHermitian v,
        (independentActualE2HilbertPhysicalGraph_mem_iff
          theta hCAR hHermitian color gamma (u, v)).mp hv⟩
  · intro hu
    obtain ⟨w, hw⟩ := (LinearPMap.mem_domain_iff).mp hu
    obtain ⟨v, hv⟩ :=
      hilbertPhysicalOutputsToActualOutputs_surjective theta hCAR hHermitian w
    apply (LinearPMap.mem_domain_iff).mpr
    refine ⟨v, ?_⟩
    rw [independentActualE2NativeHilbertChargeColumn_graph_eq]
    apply (independentActualE2HilbertPhysicalGraph_mem_iff
      theta hCAR hHermitian color gamma (u, v)).mpr
    simpa only [hv] using hw

#print axioms hilbertPhysicalOutputsToActualOutputs_surjective
#print axioms independentActualE2NativeHilbertChargeColumn_domain_iff

end
end FCP.M4F9H2D1ActualE2HilbertOutputDomainEquivalence
