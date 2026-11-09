import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPRestrictedGraphInputCut

/-!
M4F6 C2 — PROPOSED source-exact alias boundary, not yet compiled.

Past accepted M4E5 named raw-to-source equality certificates and H5E8G
scalar-congruence decomposition show that small proposition-level equalities
can avoid expanding enormous concrete terms. This deliberately tests only
the two literal DEFINITIONS whose conversion was forced in failed C2 gates.

It introduces no new graph, physical space, charge, representation witness,
axiom or additional premise, and does not assert the C2 full input cut.
It must be qualified separately before use in any C2 composition proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F6IndependentLiteralAliasBoundary
noncomputable section

open OAI.BFSSQuantum
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentPhysicalSpace
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

private abbrev μ := (volume : Measure (Boson 2))

/-- Literal independent invariant core equals the actual physical-space
preimage of the actual independent L² test-core embedding. -/
theorem independentInvariantCore_eq_actualComap
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    independentInvariantCore theta hCAR hHermitian =
      (independentPhysicalSpace theta hCAR hHermitian).comap
        (independentCoreToL2 (E := E)) := by
  rfl

/-- Literal independent unrestricted smooth-core sixteen-charge graph
equals the range of the actual independent input/charge-column product.
This is an equality of submodules, not a graph-closure or spectral claim. -/
theorem independentFullCoreGraph_eq_actualRange
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E) :
    independentFullCoreGraph color gamma theta =
      LinearMap.range
        ((independentCoreToL2 (E := E)).prod
          (independentChargeVector color gamma theta)) := by
  rfl

#print axioms independentInvariantCore_eq_actualComap
#print axioms independentFullCoreGraph_eq_actualRange

end
end FCP.M4F6IndependentLiteralAliasBoundary
