import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentSmoothSuperchargeFermion

/-!
M4E2 — independent E-valued BFSS coordinate differentiation on genuine
compactly supported smooth test functions, with exact original-source
derivative intertwining via the real-linear chain rule.

The independent operator is TestFunction.lineDerivCLM at the literal
source EuclideanSpace coordinate axis. It is defined without J and
without reference to a source operator. The unitary J appears only in
the proof of exact test-function transport.

This result does not yet claim the kinetic -i gamma theta sum, cubic
multiplication term, any whole supercharge, closed domain, or spectrum.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentSmoothSupercharge
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.IndependentSmoothCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Independent E-valued smooth directional derivative on the exact
original bosonic coordinate axis. No Fock operator or J enters this. -/
def independentCoordinateDerivative
    (i : SpaceIndex) (A : ColorIndex 2) :
    IndependentTestCore E →ₗ[ℂ] IndependentTestCore E :=
  (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single (i, A) 1)).toLinearMap

/-- The source coordinate derivative's literal real Fréchet line
derivative formula, evaluated on the independent smooth functions. -/
theorem independentCoordinateDerivative_apply
    (i : SpaceIndex) (A : ColorIndex 2)
    (f : IndependentTestCore E) (x : Boson 2) :
    independentCoordinateDerivative i A f x =
      lineDeriv ℝ (f : Boson 2 → E) x (EuclideanSpace.single (i,A) 1) := by
  change
    (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single (i,A) 1) f) x = _
  exact TestFunction.lineDerivCLM_apply_of_le (by simp)

/-- The fiber unitary commutes with the true independent coordinate
derivative, including the bosonic real Fréchet derivative convention.
This is a genuine differential-expression theorem, not a definition
by transport from the source. -/
theorem independentCoordinateDerivative_intertwining
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (i : SpaceIndex) (A : ColorIndex 2)
    (f : IndependentTestCore E) :
    independentSmoothTransport J (independentCoordinateDerivative i A f) =
      coordinateDerivative i A (independentSmoothTransport J f) := by
  apply DFunLike.ext
  intro x
  rw [independentSmoothTransport_apply,
    independentCoordinateDerivative_apply]
  change J (lineDeriv ℝ (f : Boson 2 → E) x
      (EuclideanSpace.single (i,A) 1)) =
    (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single (i,A) 1)
      (independentSmoothTransport J f)) x
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  let L : E →L[ℝ] Fermion 2 :=
    J.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have hf : DifferentiableAt ℝ (f : Boson 2 → E) x :=
    (f.contDiff.differentiable (by simp)).differentiableAt
  have ht : DifferentiableAt ℝ
      ((independentSmoothTransport J f) : Boson 2 → Fermion 2) x :=
    ((independentSmoothTransport J f).contDiff.differentiable (by simp)).differentiableAt
  rw [hf.lineDeriv_eq_fderiv, ht.lineDeriv_eq_fderiv]
  have hfun : ((independentSmoothTransport J f) : Boson 2 → Fermion 2) =
      (L ∘ (f : Boson 2 → E)) := by
    funext y
    rfl
  rw [hfun]
  have hc :
      fderiv ℝ (L ∘ (f : Boson 2 → E)) x =
        L.comp (fderiv ℝ (f : Boson 2 → E) x) := by
    exact ((L.hasFDerivAt).comp x hf.hasFDerivAt).fderiv
  rw [hc]
  rfl

#print axioms independentCoordinateDerivative
#print axioms independentCoordinateDerivative_apply
#print axioms independentCoordinateDerivative_intertwining

end
end FCP.IndependentSmoothSupercharge
