import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F7OpaqueLiteralGraphInterfaceE7D

/-!
FCP BFSS M4F7 E7K — exact SOURCE-PINNED native smooth graph map heads.

E7J Gate #1 showed that even an abstract, strictly accepted E7H
closed-product-range theorem can trigger Lean whnf timeouts when
the original independent BFSS LinearMap.comp expressions are inserted
directly into its application. This leaf isolates those *actual*
smooth input/output maps as separately named complex-linear maps.

No operator, graph, CAR relation, physical predicate, coefficient or
representation witness is changed. The definitions are J-free.
Each exact identity is compiled independently before another
source-specific graph inclusion theorem is attempted.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F7IndependentNamedSmoothGraphMapsE7K
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

/-- The exact independently constructed invariant smooth-core
inclusion into the original bosonic L² space. -/
noncomputable def independentInvariantCoreInputMap
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    independentInvariantCore theta hCAR hHermitian →ₗ[ℂ] Lp E 2 μ :=
  independentCoreToL2.comp
    (independentInvariantCore theta hCAR hHermitian).subtype

/-- The actual sixteen native independent smooth supercharges
after restriction to the original gauge-invariant smooth core. -/
noncomputable def independentInvariantCoreOutputMap
    (color : ColorIndex 2 → ColorMatrix 2)
    (gamma : SpaceIndex → GammaMatrix)
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    independentInvariantCore theta hCAR hHermitian →ₗ[ℂ]
      (SpinIndex → Lp E 2 μ) :=
  (independentChargeVector color gamma theta).comp
    (independentInvariantCore theta hCAR hHermitian).subtype

/-- No graph change: the named input is definitionally the same
input expression that appears in the accepted E7D literal graph. -/
theorem independentInvariantCoreInputMap_eq
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    independentInvariantCoreInputMap theta hCAR hHermitian =
      independentCoreToL2.comp
        (independentInvariantCore theta hCAR hHermitian).subtype := by
  rfl

#print axioms independentInvariantCoreInputMap
#print axioms independentInvariantCoreOutputMap
#print axioms independentInvariantCoreInputMap_eq

end
end FCP.M4F7IndependentNamedSmoothGraphMapsE7K
