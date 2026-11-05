import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPM3JIndependentCliffordAction
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentSpinRealization
import Mathlib.Tactic.NormNum

/-! Construct the real Clifford and genuine Spin actions from delta-one
Hermitian Majorana data alone, before selecting any module intertwiner. -/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace FCP.IndependentMajoranaAction
noncomputable section

open FCP.IndependentM3JAction
open FCP.IndependentSpinRealization

variable {I E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def normalizedGamma (theta : I → Module.End ℂ E) (i : I) : Module.End ℂ E :=
  (Real.sqrt 2 : ℂ) • theta i

variable (theta : I → Module.End ℂ E)
variable (hCAR : ∀ i j, theta i * theta j + theta j * theta i =
  (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ E))

omit [Fintype I] in
include hCAR in
theorem normalizedGamma_diag (i : I) :
    normalizedGamma theta i * normalizedGamma theta i = 1 := by
  have h := hCAR i i
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  change ((Real.sqrt 2 : ℂ) • theta i) * ((Real.sqrt 2 : ℂ) • theta i) = 1
  rw [smul_mul_smul, hs, two_smul]
  simpa using h

omit [Fintype I] in
include hCAR in
theorem normalizedGamma_anti (i j : I) (hij : i ≠ j) :
    normalizedGamma theta i * normalizedGamma theta j +
      normalizedGamma theta j * normalizedGamma theta i = 0 := by
  have h : theta i * theta j + theta j * theta i = 0 := by
    simpa [hij] using hCAR i j
  change ((Real.sqrt 2 : ℂ) • theta i) * ((Real.sqrt 2 : ℂ) • theta j) +
    ((Real.sqrt 2 : ℂ) • theta j) * ((Real.sqrt 2 : ℂ) • theta i) = 0
  rw [smul_mul_smul, smul_mul_smul, ← smul_add, h, smul_zero]

def cliffordAction :
    CliffordAlgebra (coordinateQuadratic (R := ℝ) (I := I)) →ₐ[ℝ]
      Module.End ℂ E :=
  independentRealCliffordAction (normalizedGamma theta)
    (normalizedGamma_diag theta hCAR) (normalizedGamma_anti theta hCAR)

theorem cliffordAction_generator (v : I → ℝ) :
    cliffordAction theta hCAR (CliffordAlgebra.ι _ v) =
      independentGammaReal (R := ℝ) (normalizedGamma theta) v :=
  independentRealCliffordAction_generator _ _ _ v

theorem cliffordAction_axis (i : I) :
    cliffordAction theta hCAR (CliffordAlgebra.ι _ (Pi.single i (1 : ℝ))) =
      (Real.sqrt 2 : ℂ) • theta i := by
  rw [cliffordAction_generator, independentGammaReal_axis]
  rfl

theorem cliffordAction_generator_symmetric
    (hHermitian : ∀ i, (theta i).IsSymmetric) (v : I → ℝ) :
    (cliffordAction theta hCAR (CliffordAlgebra.ι _ v)).IsSymmetric := by
  classical
  rw [cliffordAction_generator]
  have hsum : independentGammaReal (R := ℝ) (normalizedGamma theta) v =
      ∑ i, v i • normalizedGamma theta i := by
    simp only [independentGammaReal, Module.Basis.constr_apply_fintype,
      Pi.basisFun_equivFun, LinearEquiv.refl_apply]
  rw [hsum]
  apply LinearMap.isSymmetric_sum
  intro i hi
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  apply LinearMap.IsSymmetric.smul (by simp)
  exact LinearMap.IsSymmetric.smul (by simp) (hHermitian i)

/-- Genuine Hilbert-unitary Spin action constructed from the independently
given Majoranas. The construction makes no reference to a source Fock action. -/
def majoranaSpinHom [FiniteDimensional ℂ E]
    (hHermitian : ∀ i, (theta i).IsSymmetric) :
    spinGroup (coordinateQuadratic (R := ℝ) (I := I)) →* (E ≃ₗᵢ[ℂ] E) :=
  spinUnitaryHom _ (cliffordAction theta hCAR)
    (cliffordAction_generator_symmetric theta hCAR hHermitian)

#print axioms cliffordAction
#print axioms cliffordAction_axis
#print axioms cliffordAction_generator_symmetric
#print axioms majoranaSpinHom

end
end FCP.IndependentMajoranaAction
