import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7IndependentNamedSmoothGraphMapsE7K

/-!
FCP BFSS M4F7 E7K2 — exact original output map and native
literal smooth graph identification using independently accepted
E7K named map heads and E7D graph source equality.

All symbols are the actual J-free independent BFSS definitions.
Neither a physical output-membership theorem nor a source-domain
Hamiltonian identity is claimed. Avoid rfl unfolding on large
graph expressions: reuse named exact identities and simple rewrites.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7NamedSmoothGraphIdentityE7K2
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentSmoothCore
open FCP.IndependentSmoothSupercharge
open FCP.IndependentPhysicalSpace
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- The named sixteen-output map is definitionally the original
independent charge-vector map restricted to the actual invariant
smooth core. -/
theorem independentInvariantCoreOutputMap_eq
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    FCP.M4F7IndependentNamedSmoothGraphMapsE7K.independentInvariantCoreOutputMap
      color gamma theta hCAR hHermitian =
        (independentChargeVector color gamma theta).comp
          (independentInvariantCore theta hCAR hHermitian).subtype := by
  rfl

/-- Exact *source* BFSS original independent invariant smooth-core
graph relation equals the range of the two named J-free maps.
This equality has no physicality or density assumptions. -/
theorem originalLiteralCoreGraph_eq_namedProductRange
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    FCP.M4F7OpaqueLiteralGraphInterfaceE7D.literalRestrictedCoreGraphRelation
        color gamma theta hCAR hHermitian =
      LinearMap.range
        ((FCP.M4F7IndependentNamedSmoothGraphMapsE7K.independentInvariantCoreInputMap
          theta hCAR hHermitian).prod
         (FCP.M4F7IndependentNamedSmoothGraphMapsE7K.independentInvariantCoreOutputMap
          color gamma theta hCAR hHermitian)) := by
  calc
    _ = LinearMap.range
          ((independentCoreToL2.comp
            (independentInvariantCore theta hCAR hHermitian).subtype).prod
            ((independentChargeVector color gamma theta).comp
              (independentInvariantCore theta hCAR hHermitian).subtype)) :=
      FCP.M4F7OpaqueLiteralGraphInterfaceE7D.literalRestrictedCoreGraphRelation_eq
        color gamma theta hCAR hHermitian
    _ = LinearMap.range
          ((FCP.M4F7IndependentNamedSmoothGraphMapsE7K.independentInvariantCoreInputMap
            theta hCAR hHermitian).prod
           (FCP.M4F7IndependentNamedSmoothGraphMapsE7K.independentInvariantCoreOutputMap
            color gamma theta hCAR hHermitian)) := by
      rw [FCP.M4F7IndependentNamedSmoothGraphMapsE7K.independentInvariantCoreInputMap_eq,
        independentInvariantCoreOutputMap_eq]

#print axioms independentInvariantCoreOutputMap_eq
#print axioms originalLiteralCoreGraph_eq_namedProductRange

end
end FCP.M4F7NamedSmoothGraphIdentityE7K2
