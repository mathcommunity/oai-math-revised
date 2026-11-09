import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM4F8IndependentE2ConditionalPhysicalDomainDenseDD
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B10CFullHaarCoreCompatibilityAndDensityProbe

/-!
M4F8 DC — prospective *unconditional* native independent physical Hilbert
norm-density of the actual closed E2 sixteen-supercharge operator.

This is a new import boundary, NOT a strictly accepted result until the
historical source D2B10C theorem and ALL 22 genuinely original Haar
ancestors have been qualified, compiled, and made available in the same
Lean 4.34.1 / pinned Mathlib environment as accepted DD Gate #5.

The source theorem states equality of Submodule values:
  G.coreNormClosure = G.physicalSpace.
The DD hypothesis states a SET equality of L2 closure/range. The
conversion is an actual Lean theorem, not an implicit assumption.

No source-transported definition of independent E2, no alternate gauge
core, no axioms. The historical source proof still needs the separate
full source compiled ancestry. This file is NOT yet compiled.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F8IndependentE2UnconditionalPhysicalDomainDenseDC
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open FCP.BFSSSU2PhysicalDomainD2B10C
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- Source-original Haar theorem cast to DD's EXACT source core
L2 range closure (as sets), for the original paired SU(2) GaugeData.
Unconditional in statement, but the source D2B10C import is a real
and currently unqualified combined-cache dependency. -/
theorem sourceHaar_coreL2_set_closure_eq_physical :
    closure
      (LinearMap.range
        (coreToL2.comp pairedGaugeData.invariantCore.subtype) :
          Set (FullL2 2)) =
    (pairedGaugeData.physicalSpace : Set (FullL2 2)) := by
  have hsub :
      pairedGaugeData.coreNormClosure =
        pairedGaugeData.physicalSpace :=
    sourceCoreNormClosure_eq_physical_unconditional
      pairedAlgebraData pairedGaugeData
  have hset :
      (pairedGaugeData.coreNormClosure : Set (FullL2 2)) =
        (pairedGaugeData.physicalSpace : Set (FullL2 2)) :=
    congrArg (fun S : Submodule ℂ (FullL2 2) =>
      (S : Set (FullL2 2))) hsub
  simpa only [AlgebraData.GaugeData.coreNormClosure,
    Submodule.topologicalClosure_coe] using hset

/-- Unconditional Hilbert-norm density of the domain of the
ACTUAL independently constructed E2 minimal closed 16-charge
operator, in its genuinely independent physical Hilbert space.
Not graph-norm density, not yet rebased operator equivalence. -/
theorem independentE2_actual_closed_domain_dense_in_physical
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
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    Dense {v : independentPhysicalSpace theta hCAR hHermitian |
      (v : Lp E 2 μ) ∈
        (FCP.M4F7IndependentPhysicalInputCutOperatorE2.independentPhysicalInputCutClosedChargeColumn
          color gamma theta hCAR hHermitian).domain} := by
  exact FCP.M4F8IndependentE2ConditionalPhysicalDomainDenseDD.independentE2_actual_closed_domain_dense_in_physical_of_source
    color gamma theta hCAR hHermitian J hColor hGamma hJ
    sourceHaar_coreL2_set_closure_eq_physical

#print axioms sourceHaar_coreL2_set_closure_eq_physical
#print axioms independentE2_actual_closed_domain_dense_in_physical

end
end FCP.M4F8IndependentE2UnconditionalPhysicalDomainDenseDC
