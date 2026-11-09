import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F8IndependentE2UnconditionalPhysicalDomainDenseDC
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentActualClosedPhysicalOutputsE7N2

/-!
BFSS M4F8 DE2: PROSPECTIVE literal J-free full physical Hilbert
input/output graph rebase of the ACTUAL independent E2 closed
16-supercharge column.

The input is the original independent gauge-constraint submodule P
of E-valued bosonic L²; the output is its literal sixteen-coordinate
physical submodule P₁₆ of the ambient sixteen L² slots.
Neither P, P₁₆, nor the rebased operator graph is defined through
the auxiliary representation witness J.

The graph is the original E2.graph pulled back through BOTH canonical
physical inclusions. It is not an invented charge or a transported
source operator. Strictly accepted DC establishes unconditional
DENSITY of actual E2's domain in P, and E7N2 provides sixteen-output
physical membership. Their combination with this pure graph rebase
will later certify the full P-to-P₁₆ Hilbert operator's closedness,
graph/domain equivalence, and dense domain. Those claims are NOT
accepted until subsequent strict gates.

THIS FILE IS SOURCE-STAGED, UNCOMPILED, UNACCEPTED.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- Actual sixteen-slot physical output submodule of independent L².
This is the product of sixteen true J-free gauge-kernel subspaces. -/
noncomputable def independentActualPhysicalOutputs
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    Submodule ℂ (SpinIndex → Lp E 2 μ) :=
  Submodule.pi Set.univ (fun (_ : SpinIndex) =>
    independentPhysicalSpace theta hCAR hHermitian)

/-- Literal true E2 graph, pulled back along both the independent
physical input and independent sixteen-output inclusions. -/
noncomputable def independentActualE2FullPhysicalGraph
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    Submodule ℂ
      (independentPhysicalSpace theta hCAR hHermitian ×
        independentActualPhysicalOutputs theta hCAR hHermitian) :=
  (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
    color gamma theta hCAR hHermitian).graph.comap
      ((independentPhysicalSpace theta hCAR hHermitian).subtype.prodMap
        (independentActualPhysicalOutputs theta hCAR hHermitian).subtype)

/-- Pointwise equality with the ACTUAL E2 graph after both literal
inclusions, no graph replacement, no gauge definition transportation. -/
theorem independentActualE2FullPhysicalGraph_mem_iff
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (p : independentPhysicalSpace theta hCAR hHermitian ×
      independentActualPhysicalOutputs theta hCAR hHermitian) :
    p ∈ independentActualE2FullPhysicalGraph
      color gamma theta hCAR hHermitian ↔
      ((p.1 : Lp E 2 μ), (p.2 : SpinIndex → Lp E 2 μ)) ∈
        (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
          color gamma theta hCAR hHermitian).graph := by
  rfl

private theorem independentActualE2FullPhysicalGraph_vertical
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    ∀ (p : independentPhysicalSpace theta hCAR hHermitian ×
          independentActualPhysicalOutputs theta hCAR hHermitian),
      p ∈ independentActualE2FullPhysicalGraph
        color gamma theta hCAR hHermitian →
      p.1 = 0 → p.2 = 0 := by
  rintro ⟨ψ,y⟩ hp hz
  have hp' :
      ((ψ : Lp E 2 μ), (y : SpinIndex → Lp E 2 μ)) ∈
        (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
          color gamma theta hCAR hHermitian).graph :=
    (independentActualE2FullPhysicalGraph_mem_iff
      color gamma theta hCAR hHermitian _).mp hp
  have hz' : (ψ : Lp E 2 μ) = 0 :=
    congrArg (fun x : independentPhysicalSpace theta hCAR hHermitian =>
      (x : Lp E 2 μ)) hz
  have hzero : ((0 : Lp E 2 μ), (y : SpinIndex → Lp E 2 μ)) ∈
      (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
        color gamma theta hCAR hHermitian).graph := by
    simpa only [hz'] using hp'
  have hy : (y : SpinIndex → Lp E 2 μ) = 0 :=
    (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
      color gamma theta hCAR hHermitian).graph_fst_eq_zero_snd hzero rfl
  exact Subtype.ext hy

/-- The truly rebased independent E2 charge is a partial ℂ-linear
operator from the genuine independent physical Hilbert INPUT to
the genuine sixteen-slot independent physical Hilbert OUTPUT space.
It is J-free in its construction. -/
noncomputable def independentActualE2FullPhysicalChargeColumn
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    independentPhysicalSpace theta hCAR hHermitian →ₗ.[ℂ]
      independentActualPhysicalOutputs theta hCAR hHermitian :=
  (independentActualE2FullPhysicalGraph
    color gamma theta hCAR hHermitian).toLinearPMap

theorem independentActualE2FullPhysicalChargeColumn_graph_eq
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    (independentActualE2FullPhysicalChargeColumn
      color gamma theta hCAR hHermitian).graph =
      independentActualE2FullPhysicalGraph
        color gamma theta hCAR hHermitian := by
  exact Submodule.toLinearPMap_graph_eq _
    (independentActualE2FullPhysicalGraph_vertical
      color gamma theta hCAR hHermitian)

#print axioms independentActualPhysicalOutputs
#print axioms independentActualE2FullPhysicalGraph
#print axioms independentActualE2FullPhysicalGraph_mem_iff
#print axioms independentActualE2FullPhysicalChargeColumn
#print axioms independentActualE2FullPhysicalChargeColumn_graph_eq

end
end FCP.M4F8IndependentActualE2FullPhysicalGraphRebaseDE2
