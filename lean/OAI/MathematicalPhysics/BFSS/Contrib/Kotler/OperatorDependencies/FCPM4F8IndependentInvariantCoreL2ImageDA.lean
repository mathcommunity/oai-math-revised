import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentInvariantSmoothEquiv

/-!
BFSS M4F8 DA — genuine independent physical smooth-core L2 image identity.

This exact source-bound source/independent bridge uses only qualified
M4C2 physical L2 fiber-unitarity and M4D2 two-sided invariant smooth-core
equivalence. Both invariant smooth cores are independently defined;
neither one is defined as a unitary pullback of the other.

This source is a PROSPECTIVE candidate until an independent strict
Lean 4.34.1, Mathlib and axiom/cache gate accepts it. It does NOT
prove the Haar source norm density, independent physical-domain
density, rebased physical charge operator or spectral statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

namespace FCP.M4F8IndependentInvariantCoreL2ImageDA
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentSmoothCore
open FCP.IndependentFullL2GaugeTransport
open FCP.IndependentPhysicalSpace
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
private abbrev μ := (volume : Measure (Boson 2))

/-- Actual independent gauge-invariant smooth-core L2 map, before
choosing any source-intertwining unitary J. -/
noncomputable def independentInvariantCoreToL2
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric) :
    independentInvariantCore theta hCAR hHermitian →ₗ[ℂ] Lp E 2 μ :=
  independentCoreToL2.comp
    (independentInvariantCore theta hCAR hHermitian).subtype

/-- The image under the genuine fiberwise L2 unitary of the original
independently specified invariant smooth core embedding is EXACTLY the
original source GaugeData invariant-core embedding image.

The reverse inclusion invokes the accepted explicit inverse on the
actual gauge-invariant test-function subtypes; no surjectivity is assumed
for an invented surrogate smooth core. -/
theorem independentInvariantCoreToL2_unitary_image_eq_source
    (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
    (hCAR : ∀ α β A B,
      theta α A * theta β B + theta β B * theta α A =
        (if α = β ∧ A = B then (1 : ℂ) else 0) •
          (1 : Module.End ℂ E))
    (hHermitian : ∀ α A, (theta α A).IsSymmetric)
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    (fiberTransportUnitary J) ''
      (LinearMap.range
        (independentInvariantCoreToL2 theta hCAR hHermitian) :
          Set (Lp E 2 μ)) =
    (LinearMap.range
      (coreToL2.comp pairedGaugeData.invariantCore.subtype) :
        Set (FullL2 2)) := by
  let e := independentInvariantCoreLinearEquiv
    theta hCAR hHermitian J hJ
  ext v
  constructor
  · rintro ⟨u, ⟨f, rfl⟩, rfl⟩
    refine ⟨e f, ?_⟩
    change fiberTransport J (independentCoreToL2 f.val) =
      coreToL2 (independentSmoothTransport J f.val)
    exact independentSmoothTransport_coreToL2 J f.val
  · rintro ⟨f, rfl⟩
    refine ⟨independentInvariantCoreToL2 theta hCAR hHermitian
      (e.symm f), ⟨e.symm f, rfl⟩, ?_⟩
    change fiberTransport J (independentCoreToL2 (e.symm f).val) =
      coreToL2 f.val
    calc
      fiberTransport J (independentCoreToL2 (e.symm f).val) =
          coreToL2 (independentSmoothTransport J (e.symm f).val) :=
        independentSmoothTransport_coreToL2 J (e.symm f).val
      _ = coreToL2 f.val := by
        have hright : e (e.symm f) = f := e.apply_symm_apply f
        have hval : independentSmoothTransport J (e.symm f).val = f.val :=
          congrArg Subtype.val hright
        exact congrArg coreToL2 hval

#print axioms independentInvariantCoreToL2
#print axioms independentInvariantCoreToL2_unitary_image_eq_source

end
end FCP.M4F8IndependentInvariantCoreL2ImageDA
