import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7NamedClosedSmoothGraphIdentityE7K3
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7GenericOpaqueOutputConstraintE7H
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentPhysicalOutputPredicateE7I

/-!
M4F7 E7L — PROSPECTIVE conditional exact independent closed
graph all-sixteen physical-output membership using QUALIFIED
source-specific named smooth input/output maps.

This is the controlled successor to red E7J. In contrast to E7J,
the theorem hypothesis and the E7H generic application use the
separately named genuine E7K maps instead of expanding either
original independent LinearMap.comp expression.

The exact named smooth graph closure relationship must first be
qualified in E7K3. The two analytical premises remain explicit:
  hP — the original independently defined SU(2) physical L²
       submodule is closed;
  hQ — each output of the original independent smooth-core charge
       map is contained in that same physical submodule.

E6 and E7A provide accepted certificates for these premises
but are intentionally NOT recomposed here. No source-generated
operator or weakened physicality notion is introduced.

This file is STAGED only. No CI or acceptance is authorized before
strict E7K3 acceptance. The final actual E2 operator result
remains a separate theorem through E3.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7NamedConditionalPhysicalOutputBridgeE7L
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

/-- If the true physical L² space is closed and the true named
independent invariant smooth charge outputs preserve it, then
every point of the exact J-free independently defined literal
closed graph has all sixteen outputs physical. This is conditional,
not the actual E2 closed-operator graph theorem. -/
theorem originalNamedClosedGraph_subset_nativeSixteenPhysicalOutputs_of_core
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (hP : IsClosed
      ((independentPhysicalSpace theta hCAR hHermitian :
        Submodule ℂ (Lp E 2 μ)) : Set (Lp E 2 μ)))
    (hQ : ∀ (f : independentInvariantCore theta hCAR hHermitian)
      (α : SpinIndex),
        (FCP.M4F7IndependentNamedSmoothGraphMapsE7K.independentInvariantCoreOutputMap
          color gamma theta hCAR hHermitian f) α ∈
            independentPhysicalSpace theta hCAR hHermitian) :
    FCP.M4F7OpaqueLiteralGraphInterfaceE7D.literalRestrictedClosedGraphSet
        color gamma theta hCAR hHermitian ⊆
      FCP.M4F7IndependentPhysicalOutputPredicateE7I.independentAllSixteenOutputsPhysicalSet
        theta hCAR hHermitian := by
  have hAbstract :
      FCP.M4F7OpaqueLiteralGraphInterfaceE7D.literalRestrictedClosedGraphSet
        color gamma theta hCAR hHermitian ⊆
      FCP.M4F7GenericOpaqueOutputConstraintE7H.allOutputConstraint
        (I := SpinIndex) (X := Lp E 2 μ)
        (independentPhysicalSpace theta hCAR hHermitian) :=
    FCP.M4F7GenericOpaqueOutputConstraintE7H.opaque_closed_product_range_subset_allOutputConstraint
      (FCP.M4F7IndependentNamedSmoothGraphMapsE7K.independentInvariantCoreInputMap
        theta hCAR hHermitian)
      (FCP.M4F7IndependentNamedSmoothGraphMapsE7K.independentInvariantCoreOutputMap
        color gamma theta hCAR hHermitian)
      (independentPhysicalSpace theta hCAR hHermitian)
      hP hQ
      (FCP.M4F7OpaqueLiteralGraphInterfaceE7D.literalRestrictedClosedGraphSet
        color gamma theta hCAR hHermitian)
      (FCP.M4F7NamedClosedSmoothGraphIdentityE7K3.originalNamedClosedCoreGraph_eq_closure_namedProductRange
        color gamma theta hCAR hHermitian)
  intro p hp
  exact (FCP.M4F7IndependentPhysicalOutputPredicateE7I.mem_independentAllSixteenOutputsPhysicalSet_iff
    theta hCAR hHermitian p).2
    ((FCP.M4F7GenericOpaqueOutputConstraintE7H.mem_allOutputConstraint_iff
      (I := SpinIndex) (X := Lp E 2 μ)
      (independentPhysicalSpace theta hCAR hHermitian) p).mp
      (hAbstract hp))

#print axioms originalNamedClosedGraph_subset_nativeSixteenPhysicalOutputs_of_core

end
end FCP.M4F7NamedConditionalPhysicalOutputBridgeE7L
