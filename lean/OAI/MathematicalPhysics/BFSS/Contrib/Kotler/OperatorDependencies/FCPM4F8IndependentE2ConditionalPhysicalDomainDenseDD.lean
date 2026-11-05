import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F8IndependentConditionalPhysicalCoreDensityDB
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentLiteralRestrictedGraphBridgeE3

/-!
BFSS M4F8 DD — the actual independently constructed E2 physical-input-cut
closed 16-charge LinearPMap has domain norm-dense in the genuine J-free
independent physical Hilbert space, CONDITIONAL ON the exact original
source invariant-core norm-density equality.

No deformed/source operator is substituted for E2. The proof uses the
native E3 equality of the restricted smooth charge graph with the exact
invariant independent smooth-core graph, then E2 graph closure. Finally
DB transports original source physical-core density to the independent
physical Hilbert space.

This file is PROSPECTIVE / UNACCEPTED until its exact strict pinned
compiler/axiom/cache gate succeeds. No unconditional source Haar
density, graph-norm density, physical rebase, Hamiltonian or spectrum
is claimed.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.M4F8IndependentE2ConditionalPhysicalDomainDenseDD
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentPhysicalSpace
open FCP.M4F8IndependentInvariantCoreL2ImageDA
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- Native E2 smooth gauge-invariant core inputs really belong to
the domain of the ACTUAL E2 closed partial charge operator.
Proof passes through accepted E3 literal = actual raw graph,
then accepted E2 graph closure; no source transported operator. -/
theorem independentE2_smoothInvariantCore_input_mem_actual_domain
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
    (f : independentInvariantCore theta hCAR hHermitian) :
    independentInvariantCoreToL2 theta hCAR hHermitian f ∈
      (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
        color gamma theta hCAR hHermitian).domain := by
  -- Use the ACTUAL independent smooth graph map as the witness.
  -- The operator-domain question uses only its first (input) coordinate.
  let graphMap : independentInvariantCore theta hCAR hHermitian →ₗ[ℂ]
      (Lp E 2 μ × (SpinIndex → Lp E 2 μ)) :=
    (independentCoreToL2.comp
      (independentInvariantCore theta hCAR hHermitian).subtype).prod
      ((independentChargeVector color gamma theta).comp
        (independentInvariantCore theta hCAR hHermitian).subtype)
  have hgraphMap :
      graphMap f ∈
        FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutCoreGraph
          color gamma theta hCAR hHermitian := by
    apply (Set.ext_iff.mp
      (FCP.M4F7IndependentLiteralRestrictedGraphBridgeE3.independentPhysicalInputCutCoreGraph_eq_literalRestrictedRange
        color gamma theta hCAR hHermitian) (graphMap f)).2
    change graphMap f ∈ (LinearMap.range graphMap : Set _)
    exact LinearMap.mem_range_self graphMap f
  have hclosed :
      graphMap f ∈
        (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
          color gamma theta hCAR hHermitian).graph := by
    rw [FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn_graph_eq
      color gamma theta hCAR hHermitian J hColor hGamma hJ]
    exact Submodule.le_topologicalClosure _ hgraphMap
  have hfirst :
      (graphMap f).1 =
        independentInvariantCoreToL2 theta hCAR hHermitian f := by
    change independentCoreToL2 f.val =
      independentInvariantCoreToL2 theta hCAR hHermitian f
    rfl
  rw [← hfirst]
  exact LinearPMap.mem_domain_of_mem_graph hclosed

/-- True physical-subtype Hilbert-norm density of the domain of the
genuinely independent minimally CLOSED E2 sixteen-charge operator,
not an artificial source-transported operator, under the explicit
source Haar-density conclusion (not itself proved/imported here). -/
theorem independentE2_actual_closed_domain_dense_in_physical_of_source
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
    (hsource :
      closure (LinearMap.range
        (coreToL2.comp pairedGaugeData.invariantCore.subtype) :
          Set (FullL2 2)) =
        (pairedGaugeData.physicalSpace : Set (FullL2 2))) :
    Dense {v : independentPhysicalSpace theta hCAR hHermitian |
      (v : Lp E 2 μ) ∈
        (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
          color gamma theta hCAR hHermitian).domain} := by
  rw [Subtype.dense_iff]
  have hcore :
      closure (LinearMap.range
        (independentInvariantCoreToL2 theta hCAR hHermitian) :
          Set (Lp E 2 μ)) =
        (independentPhysicalSpace theta hCAR hHermitian :
          Set (Lp E 2 μ)) :=
    FCP.M4F8IndependentConditionalPhysicalCoreDensityDB.independentInvariantCoreL2_closure_eq_physical_of_source
      theta hCAR hHermitian J hJ hsource
  have hsubset :
      (LinearMap.range
        (independentInvariantCoreToL2 theta hCAR hHermitian) :
          Set (Lp E 2 μ)) ⊆
        ((↑) '' {v : independentPhysicalSpace theta hCAR hHermitian |
          (v : Lp E 2 μ) ∈
            (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
              color gamma theta hCAR hHermitian).domain} :
          Set (Lp E 2 μ)) := by
    rintro x ⟨f, rfl⟩
    have hf : independentInvariantCoreToL2 theta hCAR hHermitian f ∈
      independentPhysicalSpace theta hCAR hHermitian := f.prop
    refine ⟨⟨independentInvariantCoreToL2 theta hCAR hHermitian f, hf⟩, ?_, rfl⟩
    exact independentE2_smoothInvariantCore_input_mem_actual_domain
      color gamma theta hCAR hHermitian J hColor hGamma hJ f
  calc
    (independentPhysicalSpace theta hCAR hHermitian :
      Set (Lp E 2 μ)) =
      closure (LinearMap.range
        (independentInvariantCoreToL2 theta hCAR hHermitian) :
          Set (Lp E 2 μ)) := hcore.symm
    _ ⊆ closure
        ((↑) '' {v : independentPhysicalSpace theta hCAR hHermitian |
          (v : Lp E 2 μ) ∈
            (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
              color gamma theta hCAR hHermitian).domain} :
          Set (Lp E 2 μ)) := closure_mono hsubset

#print axioms independentE2_smoothInvariantCore_input_mem_actual_domain
#print axioms independentE2_actual_closed_domain_dense_in_physical_of_source

end
end FCP.M4F8IndependentE2ConditionalPhysicalDomainDenseDD
