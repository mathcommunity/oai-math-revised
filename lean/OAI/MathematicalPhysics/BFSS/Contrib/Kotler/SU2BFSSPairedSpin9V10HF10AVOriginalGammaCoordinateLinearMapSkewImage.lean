import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AUOriginalGammaExhaustiveNativePairLieBracket
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9SkewCoordinatePlaneSpanningProbe
import Mathlib.Algebra.Module.BigOperators

/-!
K1D18V10H-F10AV — source-native so(9) coefficient LinearMap
into the ORIGINAL real 16-dimensional gamma matrix carrier.

F10AU has now qualified the exhaustive bracket for all oriented
distinct original gamma pairs in native Mathlib so(16,R).
V9F independently supplies the exact finite spanning theorem for
the source-native SpaceIndex=Fin 9 skew matrices by F_rs=E_rs-E_sr.

This stage constructs the unique coefficient LinearMap
  rho(A) = (1/4) * sum_{r,s} A_rs * (gamma_r gamma_s)
on ALL native real 9x9 matrices. The normalization is derived:
rho(F_rs) = (1/2) gamma_r gamma_s for r!=s, exactly the
Lie-representation normalization compatible with
[F_rs,F_st]=F_rt and [gamma_r gamma_s,gamma_s gamma_t]=2 gamma_r gamma_t.

Prove only:
1. real LinearMap structure on the full source matrix carrier;
2. exact native Matrix.single evaluation;
3. exact source coordinate-plane evaluation, including diagonal zero;
4. skewness of every coordinate-plane image;
5. skewness and native Mathlib so(16,R) membership for every
   skew source input.

This gate does NOT claim arbitrary bracket preservation or a
LieHom. Those are the next independent obligations. It does not
claim global Spin(9) integration, a Spin(48) lift, Fock action,
or BFSS physical/spectral results.

No replacement gamma basis, source-label permutation, guessed
coefficient normalization, axioms, admits, linter suppression,
or increased proof limits. Candidate until pinned strict
Lean 4.34.1 warnings-as-errors compilation and independent
complete declaration type/root-axiom audits pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open FCP.BFSSPairedSpin9Plane
open OAI.BFSSQuantum
open Matrix
open scoped BigOperators

/-- Exact finite coefficient lift from every native 9x9 real
matrix to the ORIGINAL real 16x16 gamma-matrix carrier. -/
noncomputable def coordinateToOriginalGammaFiniteLift
    (A : Matrix SpaceIndex SpaceIndex ℝ) : GammaMatrix :=
  (1 / 4 : ℝ) •
    ∑ r : SpaceIndex, ∑ s : SpaceIndex,
      (A r s) • (gamma r * gamma s)

/-- The original gamma coefficient lift is a genuine real LinearMap
on the full native 9x9 matrix carrier. -/
noncomputable def coordinateToOriginalGammaLinearMap :
    Matrix SpaceIndex SpaceIndex ℝ →ₗ[ℝ] GammaMatrix where
  toFun := coordinateToOriginalGammaFiniteLift
  map_add' := by
    intro A B
    simp only [coordinateToOriginalGammaFiniteLift, Matrix.add_apply,
      add_smul, Finset.sum_add_distrib, smul_add]
  map_smul' := by
    intro c A
    simp only [coordinateToOriginalGammaFiniteLift, Matrix.smul_apply,
      Finset.smul_sum, smul_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    exact congrArg (fun z : ℝ => z • (gamma r * gamma s))
      (show (1 / 4 : ℝ) * (c * A r s) =
        c * ((1 / 4 : ℝ) * A r s) by ring)

/-- Unfolding the typed coefficient map exposes its exact
source-original finite lift without changing labels. -/
theorem coordinateToOriginalGammaLinearMap_apply
    (A : Matrix SpaceIndex SpaceIndex ℝ) :
    coordinateToOriginalGammaLinearMap A =
      coordinateToOriginalGammaFiniteLift A := rfl

/-- Exact evaluation of the source-native real LinearMap on
Mathlib's literal single-entry matrix E_rs. -/
theorem coordinateToOriginalGammaLinearMap_matrixUnit
    (r s : SpaceIndex) :
    coordinateToOriginalGammaLinearMap
      (Matrix.single r s (1 : ℝ) :
        Matrix SpaceIndex SpaceIndex ℝ) =
      (1 / 4 : ℝ) • (gamma r * gamma s) := by
  rw [coordinateToOriginalGammaLinearMap_apply]
  unfold coordinateToOriginalGammaFiniteLift
  congr 1
  rw [Finset.sum_eq_single r]
  · rw [Finset.sum_eq_single s]
    · simp
    · intro y _ hy
      simp [hy.symm]
    · simp
  · intro x _ hx
    simp [hx.symm]
  · simp

/-- The original gamma coefficient map sends the native source
coordinate plane F_rs=E_rs-E_sr to one half of gamma_r gamma_s
when r!=s, and to zero on the diagonal. -/
theorem coordinateToOriginalGammaLinearMap_coordinatePlane
    (r s : SpaceIndex) :
    coordinateToOriginalGammaLinearMap (coordinatePlane9 r s) =
      if _hrs : r = s then
        (0 : GammaMatrix)
      else
        (1 / 2 : ℝ) • (gamma r * gamma s) := by
  by_cases hrs : r = s
  · subst s
    simp [coordinatePlane9_self]
  · rw [dite_eq_right hrs]
    rw [coordinatePlane9_eq_single_sub_single, map_sub,
      coordinateToOriginalGammaLinearMap_matrixUnit,
      coordinateToOriginalGammaLinearMap_matrixUnit]
    rw [source9OriginalGamma_anticommute s r (Ne.symm hrs)]
    rw [smul_neg, sub_neg_eq_add, ← add_smul]
    norm_num

/-- Every original gamma image of a native source coordinate plane
is skew-symmetric, including the zero diagonal plane. -/
theorem coordinateToOriginalGammaLinearMap_coordinatePlane_transpose
    (r s : SpaceIndex) :
    (coordinateToOriginalGammaLinearMap (coordinatePlane9 r s)).transpose =
      -(coordinateToOriginalGammaLinearMap (coordinatePlane9 r s)) := by
  by_cases hrs : r = s
  · subst s
    simp [coordinateToOriginalGammaLinearMap_coordinatePlane]
  · rw [coordinateToOriginalGammaLinearMap_coordinatePlane]
    rw [dite_eq_right hrs]
    change
      ((1 / 2 : ℝ) • (gamma r * gamma s)).transpose =
        -((1 / 2 : ℝ) • (gamma r * gamma s))
    calc
      ((1 / 2 : ℝ) • (gamma r * gamma s)).transpose =
          (1 / 2 : ℝ) • (gamma s * gamma r) := by
            rw [Matrix.transpose_smul, Matrix.transpose_mul,
              gamma_symmetric s, gamma_symmetric r]
      _ = -((1 / 2 : ℝ) • (gamma r * gamma s)) := by
            rw [source9OriginalGamma_anticommute s r (Ne.symm hrs), smul_neg]

/-- The exact coefficient LinearMap sends EVERY skew native 9x9
source matrix to a skew original 16x16 gamma matrix. This uses
the already-qualified full coordinate-plane spanning theorem. -/
theorem coordinateToOriginalGammaLinearMap_image_transpose
    (A : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A.transpose = -A) :
    (coordinateToOriginalGammaLinearMap A).transpose =
      -(coordinateToOriginalGammaLinearMap A) := by
  rw [coordinateSkewMatrix9_plane_spanning A hA]
  simp only [map_smul, map_sum, Matrix.transpose_smul,
    Matrix.transpose_sum,
    coordinateToOriginalGammaLinearMap_coordinatePlane_transpose,
    smul_neg, Finset.sum_neg_distrib]

/-- Every skew source-native 9x9 input is mapped into the
actual pinned Mathlib native real orthogonal Lie subalgebra so(16). -/
theorem coordinateToOriginalGammaLinearMap_image_mem_so
    (A : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A.transpose = -A) :
    coordinateToOriginalGammaLinearMap A ∈
      LieAlgebra.Orthogonal.so SpinIndex ℝ := by
  rw [LieAlgebra.Orthogonal.mem_so]
  exact coordinateToOriginalGammaLinearMap_image_transpose A hA

#print axioms coordinateToOriginalGammaFiniteLift
#print axioms coordinateToOriginalGammaLinearMap
#print axioms coordinateToOriginalGammaLinearMap_apply
#print axioms coordinateToOriginalGammaLinearMap_matrixUnit
#print axioms coordinateToOriginalGammaLinearMap_coordinatePlane
#print axioms coordinateToOriginalGammaLinearMap_coordinatePlane_transpose
#print axioms coordinateToOriginalGammaLinearMap_image_transpose
#print axioms coordinateToOriginalGammaLinearMap_image_mem_so

end
end FCP.BFSSPairedSpin9Clifford
