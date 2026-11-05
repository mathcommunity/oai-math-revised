import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentSmoothCore

/-!
M4D2 — genuine two-sided complex-linear equivalence of independent and
original smooth compactly supported BFSS test functions, restricted to
their literal gauge-invariant cores.

The inverse is constructed by Mathlib TestFunction.postcompCLM J.symm,
not by assuming a transported core. Membership is supplied by the
qualified M4D1 AE-L2 invariant-core iff theorem.
No differential supercharge, closed graph, or spectrum is claimed.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentSmoothCore
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG4J
open FCP.IndependentPhysicalSpace
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The inverse fiber J.symm induces a bounded postcomposition operator
on actual original-source test functions. -/
def independentSmoothInverse (J : E ≃ₗᵢ[ℂ] Fermion 2) :
    SmoothCore 2 →L[ℂ] IndependentTestCore E :=
  TestFunction.postcompCLM J.symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Exact two-sided smooth compactly supported complex-linear equivalence;
both inverse laws are proved pointwise on the actual TestFunction types. -/
def independentSmoothLinearEquiv
    (J : E ≃ₗᵢ[ℂ] Fermion 2) :
    IndependentTestCore E ≃ₗ[ℂ] SmoothCore 2 where
  toFun := independentSmoothTransport J
  invFun := independentSmoothInverse J
  left_inv := by
    intro f
    apply DFunLike.ext
    intro x
    change J.symm (J (f x)) = f x
    exact J.symm_apply_apply (f x)
  right_inv := by
    intro f
    apply DFunLike.ext
    intro x
    change J (J.symm (f x)) = f x
    exact J.apply_symm_apply (f x)
  map_add' := (independentSmoothTransport J).map_add
  map_smul' := (independentSmoothTransport J).map_smul

variable [FiniteDimensional ℂ E]
variable (theta : SpinIndex → ColorIndex 2 → Module.End ℂ E)
variable (hCAR : ∀ α β A B,
  theta α A * theta β B + theta β B * theta α A =
    (if α = β ∧ A = B then (1 : ℂ) else 0) • (1 : Module.End ℂ E))
variable (hHermitian : ∀ α A, (theta α A).IsSymmetric)

/-- Exact complex-linear bijection between the INDEPENDENT invariant
smooth test-function core and the LITERAL original source invariantCore.
Both subtype witnesses follow from M4D1; none is manufactured by defining
either invariant core as the image of the other. -/
def independentInvariantCoreLinearEquiv
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (hJ : ∀ α A w, J (theta α A w) = pairedTheta α A (J w)) :
    independentInvariantCore theta hCAR hHermitian ≃ₗ[ℂ]
      pairedGaugeData.invariantCore where
  toFun f :=
    ⟨independentSmoothLinearEquiv J f.val,
      (independentInvariantCore_iff_source theta hCAR hHermitian J hJ f.val).mp f.prop⟩
  invFun f :=
    ⟨(independentSmoothLinearEquiv J).symm f.val,
      (independentInvariantCore_iff_source theta hCAR hHermitian J hJ
        ((independentSmoothLinearEquiv J).symm f.val)).mpr
          (by
            have hright :
                (independentSmoothLinearEquiv J)
                  ((independentSmoothLinearEquiv J).symm f.val) = f.val :=
              (independentSmoothLinearEquiv J).apply_symm_apply f.val
            exact hright.symm ▸ f.prop)⟩
  left_inv := by
    intro f
    apply Subtype.ext
    exact (independentSmoothLinearEquiv J).symm_apply_apply f.val
  right_inv := by
    intro f
    apply Subtype.ext
    exact (independentSmoothLinearEquiv J).apply_symm_apply f.val
  map_add' := by
    intro f g
    apply Subtype.ext
    exact (independentSmoothLinearEquiv J).map_add f.val g.val
  map_smul' := by
    intro c f
    apply Subtype.ext
    exact (independentSmoothLinearEquiv J).map_smul c f.val

#print axioms independentSmoothInverse
#print axioms independentSmoothLinearEquiv
#print axioms independentInvariantCoreLinearEquiv

end
end FCP.IndependentSmoothCore
