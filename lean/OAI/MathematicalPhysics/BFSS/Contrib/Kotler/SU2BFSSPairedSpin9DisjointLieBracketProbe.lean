import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9PlaneGeneratorProbe

/-!
K1D18V8C — disjoint-plane Lie bracket on the exact original paired
48-real BFSS source labels.

For four distinct spatial indices, the actual doubled plane generators
constructed by V8A commute. This is only the complementary disjoint-plane
case, not full so(9), a global Lie group or Fock action, or BFSS physics.
The original gamma and paired label source remain fixed; no proof limits.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSGamma9
open scoped Kronecker

private theorem gamma_cross_swap (a b : SpaceIndex) (hab : a ≠ b) :
    gamma a * gamma b = -(gamma b * gamma a) := by
  have h : gamma b * gamma a + gamma a * gamma b = 0 := by
    simpa [Ne.symm hab] using (FCP.BFSSGamma9.gamma_clifford b a)
  calc
    gamma a * gamma b =
        (gamma b * gamma a + gamma a * gamma b) - gamma b * gamma a := by
      abel
    _ = -(gamma b * gamma a) := by rw [h]; simp

/-- An element anticommuting with each of two factors commutes with
their ordered product; a typed matrix lemma, not a heuristic sign count. -/
private theorem commute_pair_of_cross_swaps
    (A B C : GammaMatrix)
    (hAB : A * B = -(B * A))
    (hAC : A * C = -(C * A)) :
    A * (B * C) = (B * C) * A := by
  calc
    A * (B * C) = (A * B) * C := by rw [← mul_assoc]
    _ = (-(B * A)) * C := by rw [hAB]
    _ = -(B * (A * C)) := by simp only [neg_mul, mul_assoc]
    _ = -(B * (-(C * A))) := by rw [hAC]
    _ = B * (C * A) := by simp only [mul_neg, neg_neg]
    _ = (B * C) * A := by rw [mul_assoc]

private theorem gamma_disjoint_planes_mul_commute
    (r s t u : SpaceIndex)
    (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t) (hsu : s ≠ u) :
    (gamma r * gamma s) * (gamma t * gamma u) =
      (gamma t * gamma u) * (gamma r * gamma s) := by
  have hr : gamma r * (gamma t * gamma u) =
      (gamma t * gamma u) * gamma r :=
    commute_pair_of_cross_swaps (gamma r) (gamma t) (gamma u)
      (gamma_cross_swap r t hrt) (gamma_cross_swap r u hru)
  have hs : gamma s * (gamma t * gamma u) =
      (gamma t * gamma u) * gamma s :=
    commute_pair_of_cross_swaps (gamma s) (gamma t) (gamma u)
      (gamma_cross_swap s t hst) (gamma_cross_swap s u hsu)
  calc
    (gamma r * gamma s) * (gamma t * gamma u) =
        gamma r * (gamma s * (gamma t * gamma u)) := by
      simp only [mul_assoc]
    _ = gamma r * ((gamma t * gamma u) * gamma s) := by rw [hs]
    _ = (gamma r * (gamma t * gamma u)) * gamma s := by
      simp only [mul_assoc]
    _ = ((gamma t * gamma u) * gamma r) * gamma s := by rw [hr]
    _ = (gamma t * gamma u) * (gamma r * gamma s) := by
      simp only [mul_assoc]

private theorem plane16_disjoint_mul_commute
    (r s t u : SpaceIndex)
    (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t) (hsu : s ≠ u) :
    plane16 r s * plane16 t u =
      plane16 t u * plane16 r s := by
  simpa only [plane16, neg_mul_neg] using
    (gamma_disjoint_planes_mul_commute r s t u hrt hru hst hsu)

private theorem blockPlane_mul (r s t u : SpaceIndex) :
    ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s) *
        ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 t u) =
      ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ
        (plane16 r s * plane16 t u)) := by
  simpa only [one_mul] using
    (Matrix.mul_kronecker_mul
      (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ)
      (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ)
      (plane16 r s) (plane16 t u)).symm

private theorem blockPlanes_disjoint_mul_commute
    (r s t u : SpaceIndex)
    (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t) (hsu : s ≠ u) :
    ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s) *
        ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 t u) =
      ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 t u) *
        ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s) := by
  rw [blockPlane_mul r s t u, blockPlane_mul t u r s,
    plane16_disjoint_mul_commute r s t u hrt hru hst hsu]

/-- Exact original paired-Fock 48-label doubled Spin(9) generator bracket,
for four pairwise distinct spatial labels. -/
theorem originalPairedPlane_disjoint_bracket
    (r s t u : SpaceIndex)
    (_hrs : r ≠ s) (_htu : t ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t) (hsu : s ≠ u) :
    originalPairedPlane r s * originalPairedPlane t u -
        originalPairedPlane t u * originalPairedPlane r s =
      0 := by
  apply sub_eq_zero.mpr
  let E := Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv
  let B (a b : SpaceIndex) :
      Matrix (ColorIndex 2 × SpinIndex) (ColorIndex 2 × SpinIndex) ℝ :=
    (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 a b
  have h : B r s * B t u = B t u * B r s :=
    blockPlanes_disjoint_mul_commute r s t u hrt hru hst hsu
  change E (B r s) * E (B t u) = E (B t u) * E (B r s)
  calc
    E (B r s) * E (B t u) =
        E (B r s * B t u) := by rw [map_mul]
    _ = E (B t u * B r s) := congrArg E h
    _ = E (B t u) * E (B r s) := by rw [map_mul]

#print axioms originalPairedPlane_disjoint_bracket

end
end FCP.BFSSPairedSpin9Plane
