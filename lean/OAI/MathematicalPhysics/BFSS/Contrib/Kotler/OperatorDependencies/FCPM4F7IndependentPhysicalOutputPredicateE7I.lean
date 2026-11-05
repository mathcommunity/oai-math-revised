import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentClosedChargePhysicalInputE6

/-!
M4F7 E7I — the EXACT native independent all-sixteen-outputs
SU(2)-physical Hilbert-space predicate, factored from any graph.

The physical space is still the previously accepted, genuinely
J-free `independentPhysicalSpace theta hCAR hHermitian`.
No charge map, closed graph, source identity, representation
witness J, closure manipulation or Hilbert rebasing occurs here.
The predicate applies to a product of ambient original independent
L² input with a 16-component ambient independent L² output.

This is a typed source-specific support interface, NOT yet a theorem
that E2's closed operator satisfies the predicate.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7IndependentPhysicalOutputPredicateE7I
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- Source-exact independent predicate: *all* sixteen entries of a
graph point's output lie in the original independent physical L²
submodule. No source-transferred or weakened definition. -/
noncomputable def independentAllSixteenOutputsPhysicalSet
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ)) :=
  {p | ∀ α : SpinIndex,
    p.2 α ∈ independentPhysicalSpace theta hCAR hHermitian}

/-- Pure membership equivalence, independent of any BFSS operator.
This is the exact sixteen-coordinate, not an arbitrary subspace,
criterion subsequently used for graph inclusion. -/
theorem mem_independentAllSixteenOutputsPhysicalSet_iff
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (p : Lp E 2 μ × (SpinIndex → Lp E 2 μ)) :
    p ∈ independentAllSixteenOutputsPhysicalSet theta hCAR hHermitian ↔
      ∀ α : SpinIndex,
        p.2 α ∈ independentPhysicalSpace theta hCAR hHermitian := by
  rfl

#print axioms independentAllSixteenOutputsPhysicalSet
#print axioms mem_independentAllSixteenOutputsPhysicalSet_iff

end
end FCP.M4F7IndependentPhysicalOutputPredicateE7I
