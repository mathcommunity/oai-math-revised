import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F6GenericNamedAliasInputCut
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F6IndependentLiteralAliasBoundary

/-!
M4F6 C2 — independently constructed 16-charge input-restriction certificate.

Source-independent graph maps, source-independent gauge-invariant test core.
The membership predicate is the actual independent physical Hilbert submodule,
not a transported definition or an assumed charge-preserving condition.

Candidate only: deliberately staged without CI pending C1 source verdict.
The conclusion is input-restricted smooth-core graph equality, NOT graph
closability, output physical membership, a closed operator or Hamiltonian.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.M4F6IndependentGraphInputCut
noncomputable section

open OAI.BFSSQuantum
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentPhysicalSpace
open FCP.RestrictedGraphInputCut
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- Exact independent restriction of the concrete sixteen-charge smooth
core graph to independently defined gauge-invariant input sections. -/
theorem independentCoreGraph_eq_physicalInputCut
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    (LinearMap.range
      ((independentCoreToL2.comp
        (independentInvariantCore theta hCAR hHermitian).subtype).prod
        ((independentChargeVector color gamma theta).comp
          (independentInvariantCore theta hCAR hHermitian).subtype)) :
        Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) =
      {p | p ∈ independentFullCoreGraph color gamma theta ∧
        p.1 ∈ independentPhysicalSpace theta hCAR hHermitian} := by
  exact FCP.M4F6GenericNamedAliasInputCut.core_graph_input_cut_with_named_aliases
    (independentCoreToL2 (E := E))
    (independentChargeVector color gamma theta)
    (independentPhysicalSpace theta hCAR hHermitian)
    (independentInvariantCore theta hCAR hHermitian)
    (independentFullCoreGraph color gamma theta)
    (FCP.M4F6IndependentLiteralAliasBoundary.independentInvariantCore_eq_actualComap
      theta hCAR hHermitian)
    (FCP.M4F6IndependentLiteralAliasBoundary.independentFullCoreGraph_eq_actualRange
      color gamma theta)

#print axioms independentCoreGraph_eq_physicalInputCut
#check independentCoreGraph_eq_physicalInputCut

end
end FCP.M4F6IndependentGraphInputCut
