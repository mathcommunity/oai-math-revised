import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7NamedSmoothGraphIdentityE7K2

/-!
FCP BFSS M4F7 E7K3 — the genuine independent literal restricted
SMOOTH GRAPH CLOSURE equals the ordinary closure of the named
source-exact E7K input/output product-map range.

Reuse the STRICTLY accepted E7K2 raw relation equality and a
typed congrArg on set closure, without reflexive expansion of
the original 16-charge product map. This leaf contains no new
physical output, closed operator identity, source transport,
Hilbert density or Hamiltonian theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7NamedClosedSmoothGraphIdentityE7K3
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

/-- The accepted original independent restricted closed graph alias
is EXACTLY the set closure of the range of the two genuine J-free,
independently defined complex-linear smooth-core graph maps. -/
theorem originalNamedClosedCoreGraph_eq_closure_namedProductRange
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    FCP.M4F7OpaqueLiteralGraphInterfaceE7D.literalRestrictedClosedGraphSet
      color gamma theta hCAR hHermitian =
    closure (LinearMap.range
      ((FCP.M4F7IndependentNamedSmoothGraphMapsE7K.independentInvariantCoreInputMap
        theta hCAR hHermitian).prod
       (FCP.M4F7IndependentNamedSmoothGraphMapsE7K.independentInvariantCoreOutputMap
        color gamma theta hCAR hHermitian)) :
      Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))) := by
  unfold FCP.M4F7OpaqueLiteralGraphInterfaceE7D.literalRestrictedClosedGraphSet
  exact congrArg
    (fun S : Submodule ℂ (Lp E 2 μ × (SpinIndex → Lp E 2 μ)) =>
      closure (S : Set (Lp E 2 μ × (SpinIndex → Lp E 2 μ))))
    (FCP.M4F7NamedSmoothGraphIdentityE7K2.originalLiteralCoreGraph_eq_namedProductRange
      color gamma theta hCAR hHermitian)

#print axioms originalNamedClosedCoreGraph_eq_closure_namedProductRange

end
end FCP.M4F7NamedClosedSmoothGraphIdentityE7K3
