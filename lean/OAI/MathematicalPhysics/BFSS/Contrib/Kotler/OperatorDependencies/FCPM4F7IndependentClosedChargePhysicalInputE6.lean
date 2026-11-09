import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentLiteralRestrictedGraphBridgeE3

/-!
M4F7 E6 — source-exact *independent* true physical-input preservation
for the J-free E2 closed sixteen-charge minimal partial operator.

This source does NOT import historical D1/G4K9D. It closes the genuine
input-domain question inside the native independent physical subspace,
using its already strictly accepted M4C3 membership equivalence,
the source's original closed physical submodule, E2 closed-graph identity
and E3 named typed membership adapter.

Every graph input is shown physically invariant, NOT automatically dense.
No statement about sixteen physical outputs, rebased physical Hilbert
codomain, the source named deformedModelGraph, Hamiltonian, or spectrum.
No independent operator or graph definition is changed.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7IndependentClosedChargePhysicalInputE6
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.IndependentFullL2GaugeTransport
open FCP.IndependentSmoothSupercharge
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- Genuine independent gauge-constraint physical subspace is closed
in its ambient L² Hilbert space. Its DEFINITION is independent of J;
J is only used to identify it with the original source physical subspace
for the closure proof. -/
theorem independentPhysicalSpace_isClosed
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    IsClosed ((independentPhysicalSpace theta hCAR hHermitian :
      Submodule ℂ (Lp E 2 μ)) : Set (Lp E 2 μ)) := by
  have hset :
      (independentPhysicalSpace theta hCAR hHermitian :
        Set (Lp E 2 μ)) =
      {v : Lp E 2 μ |
        fiberTransport J v ∈ pairedGaugeData.physicalSpace} := by
    ext v
    exact independentPhysicalSpace_iff_source
      theta hCAR hHermitian J hJ v
  rw [hset]
  exact pairedGaugeData.physicalSpace_closed.preimage
    (fiberTransportUnitary J).continuous

/-- The actual J-free E2 minimal CLOSED physical-input-cut charge column
takes every graph input from the genuinely independent SU(2)-physical L²
subspace, not merely from ambient L². This uses ONLY E2/E3 native
independent graph correspondence and closure under physical constraints.
The output codomain remains ambient 16-slot L², not yet rebased. -/
theorem independentPhysicalInputCutClosedChargeColumn_input_physical
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
    (p : Lp E 2 μ × (SpinIndex → Lp E 2 μ))
    (hp : p ∈
      ((FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
        color gamma theta hCAR hHermitian).graph :
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ)))) :
    p.1 ∈ independentPhysicalSpace theta hCAR hHermitian := by
  have hclosed : IsClosed
      {q : Lp E 2 μ × (SpinIndex → Lp E 2 μ) |
        q.1 ∈ independentPhysicalSpace theta hCAR hHermitian} :=
    (independentPhysicalSpace_isClosed theta hCAR hHermitian J hJ).preimage
      continuous_fst
  have hcore : (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutCoreGraph
      color gamma theta hCAR hHermitian :
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) ⊆
      {q : Lp E 2 μ × (SpinIndex → Lp E 2 μ) |
        q.1 ∈ independentPhysicalSpace theta hCAR hHermitian} := by
    intro q hq
    exact ((FCP.M4F7IndependentLiteralRestrictedGraphBridgeE3.independentPhysicalInputCutCoreGraph_mem_iff
      color gamma theta hCAR hHermitian q).mp hq).2
  have hclosure := closure_minimal hcore hclosed
  rw [FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn_graph_eq
    color gamma theta hCAR hHermitian J hColor hGamma hJ,
    Submodule.topologicalClosure_coe] at hp
  exact hclosure hp

#print axioms independentPhysicalSpace_isClosed
#print axioms independentPhysicalInputCutClosedChargeColumn_input_physical

end
end FCP.M4F7IndependentClosedChargePhysicalInputE6
