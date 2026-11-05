import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentChargeOutputTypedE7A
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7GenericClosedRangeOutputsE7G
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentClosedChargePhysicalInputE6

/-!
M4F7 E7D — exact opaque named interfaces for the ORIGINAL
independent literal restricted smooth-core product-range graph.

Following E7B/E7C declaration-level whnf failures, this module
first ONLY defines named source-exact graph interfaces and certifies
their literal equality. It does not assert closed-output invariance.
E7A, E7G and E6 remain separately qualified dependencies.

The definitions contain no representation witness J, no substitution
of a source-transported operator, no altered charge, and no new
mathematical axioms. Each exact identity must kernel-check before
being used in a later physically relevant theorem.

The restriction is proof-engineering opacity, never a change of
mathematical target.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7OpaqueLiteralGraphInterfaceE7D
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentPhysicalSpace
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- J-free named copy of the ACTUAL original smooth invariant-core
graph product linear range. Definitional equality is certified below. -/
noncomputable def literalRestrictedCoreGraphRelation
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    Submodule ℂ (Lp E 2 μ × (SpinIndex → Lp E 2 μ)) :=
  LinearMap.range
    ((independentCoreToL2.comp
      (independentInvariantCore theta hCAR hHermitian).subtype).prod
      ((independentChargeVector color gamma theta).comp
        (independentInvariantCore theta hCAR hHermitian).subtype))

/-- Exact opaque set-valued ordinary closure of the independent
literal restricted core graph, NOT a surrogate charge operator. -/
noncomputable def literalRestrictedClosedGraphSet
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ)) :=
  closure (literalRestrictedCoreGraphRelation
    color gamma theta hCAR hHermitian : Set _)

/-- Every exact source level of the representation is preserved;
the alias expands definitionally to the original E3 literal range. -/
theorem literalRestrictedCoreGraphRelation_eq
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    literalRestrictedCoreGraphRelation color gamma theta hCAR hHermitian =
      LinearMap.range
        ((independentCoreToL2.comp
          (independentInvariantCore theta hCAR hHermitian).subtype).prod
          ((independentChargeVector color gamma theta).comp
            (independentInvariantCore theta hCAR hHermitian).subtype)) := by
  rfl

/-- The opaque closure is *definitionally identical* to the precise
original literal restricted graph closure used by accepted E3. -/
theorem literalRestrictedClosedGraphSet_eq
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    literalRestrictedClosedGraphSet color gamma theta hCAR hHermitian =
    closure (LinearMap.range
      ((independentCoreToL2.comp
        (independentInvariantCore theta hCAR hHermitian).subtype).prod
        ((independentChargeVector color gamma theta).comp
          (independentInvariantCore theta hCAR hHermitian).subtype))) := by
  unfold literalRestrictedClosedGraphSet
  exact congrArg
    (fun S : Submodule ℂ (Lp E 2 μ × (SpinIndex → Lp E 2 μ)) =>
      closure (S : Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))))
    (literalRestrictedCoreGraphRelation_eq color gamma theta hCAR hHermitian)

#print axioms literalRestrictedCoreGraphRelation
#print axioms literalRestrictedClosedGraphSet
#print axioms literalRestrictedCoreGraphRelation_eq
#print axioms literalRestrictedClosedGraphSet_eq

end
end FCP.M4F7OpaqueLiteralGraphInterfaceE7D
