import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Analysis.Complex.Basic

/-!
New research lemma: extend an actual generator intertwiner to the entire
real Clifford algebra. Neither algebra action is defined by transport.
No irreducibility, invertibility, adjoint convention or scalar phase is needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.IndependentCliffordIntertwining
noncomputable section

variable {M E F : Type*}
variable [AddCommGroup M] [Module ℝ M]
variable [AddCommGroup E] [Module ℂ E]
variable [AddCommGroup F] [Module ℂ F]

/-- Agreement on every real Clifford generator implies agreement on every
Clifford element, as an equality on vectors. -/
theorem intertwines_all
    (Q : QuadraticForm ℝ M)
    (rho : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ E)
    (sigma : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ F)
    (T : E →ₗ[ℂ] F)
    (hgen : ∀ (v : M) (w : E),
      T (rho (CliffordAlgebra.ι Q v) w) =
        sigma (CliffordAlgebra.ι Q v) (T w))
    (x : CliffordAlgebra Q) (w : E) :
    T (rho x w) = sigma x (T w) := by
  have hall : ∀ y : CliffordAlgebra Q, ∀ z : E,
      T (rho y z) = sigma y (T z) := by
    intro y
    induction y using CliffordAlgebra.induction with
    | algebraMap r =>
        intro z
        rw [rho.commutes r, sigma.commutes r]
        simp only [Algebra.algebraMap_eq_smul_one,
          LinearMap.smul_apply, Module.End.one_apply]
        exact (T.restrictScalars ℝ).map_smul r z
    | ι v => exact hgen v
    | mul a b ha hb =>
        intro z
        simp only [map_mul, Module.End.mul_apply]
        rw [ha, hb]
    | add a b ha hb =>
        intro z
        simp only [map_add, LinearMap.add_apply]
        rw [ha, hb]
  exact hall x w

/-- On a finite real coordinate space, it suffices to intertwine just the
coordinate-axis generators. This keeps source adapters at their accepted
basis interfaces, without unfolding concrete finite Fock sums. -/
theorem intertwines_all_of_coordinate_axes
    {I : Type*} [Fintype I] [DecidableEq I]
    (Q : QuadraticForm ℝ (I → ℝ))
    (rho : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ E)
    (sigma : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ F)
    (T : E →ₗ[ℂ] F)
    (haxis : ∀ (i : I) (w : E),
      T (rho (CliffordAlgebra.ι Q (Pi.single i (1 : ℝ))) w) =
        sigma (CliffordAlgebra.ι Q (Pi.single i (1 : ℝ))) (T w))
    (x : CliffordAlgebra Q) (w : E) :
    T (rho x w) = sigma x (T w) := by
  apply intertwines_all Q rho sigma T _ x w
  intro v z
  have hexp : v = ∑ i : I, v i • Pi.single i (1 : ℝ) := by
    funext i
    simp [Pi.single_apply]
  have hreal (r : ℝ) (y : E) : T (r • y) = r • T y :=
    (T.restrictScalars ℝ).map_smul r y
  rw [hexp]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    hreal]
  apply Finset.sum_congr rfl
  intro i hi
  rw [haxis]

#print axioms intertwines_all
#print axioms intertwines_all_of_coordinate_axes

end
end FCP.IndependentCliffordIntertwining
