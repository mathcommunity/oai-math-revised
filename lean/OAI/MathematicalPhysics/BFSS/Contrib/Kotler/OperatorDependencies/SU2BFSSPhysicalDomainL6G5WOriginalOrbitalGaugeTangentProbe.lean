import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5VOriginalRightOrderedMixedOperatorProbe
import OAI.MathematicalPhysics.BFSS.NormalLinearization

/-!
L6G5W — source-defined infinitesimal gauge action for the proved
right-ordered mixed first-order SmoothCore operator.

The pinned original source defines gaugeTangent x z through its
colorLie z (spatialColor x i). We use precisely that definition,
rather than invent a gauge generator, and preserve the -i sign.

This establishes the ORBITAL tangent contribution only. The full
physical Gauss constraint includes the fermion representation and is
not replaced or assumed here. No spectral theorem follows.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5W
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G5P
open FCP.BFSSSU2PhysicalDomainL6G5V

/-- The source color Lie bracket is linear in its FIRST argument;
make that already-proved source property available to finite map_sum.
No algebraic hypotheses beyond the pinned AlgebraData. -/
private def sourceColorLieFirstLinear {N : ℕ}
    (M : AlgebraData N) (q : ColorVector N) :
    ColorVector N →ₗ[ℝ] ColorVector N where
  toFun z := M.colorLie z q
  map_add' z t := M.colorLie_add_left z t q
  map_smul' r z := M.colorLie_smul_left r z q

/-- Canonical ORIGINAL source color-vector direction selected by the
real spinor w: sum of each actual spatial color vector, weighted by
its original symmetric gamma quadratic coefficient. -/
def sourceSpinorWeightedColor {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ) (x : Boson N) :
    ColorVector N :=
  ∑ k : SpaceIndex,
    (dotProduct w (M.gamma k *ᵥ w)) • spatialColor x k

/-- The actual source infinitesimal gauge tangent, evaluated at the
spinor-weighted source color vector, is MINUS the original color
bracket contraction. This is a pointwise SOURCE theorem, not a formal
replacement for the pinned gauge action. -/
theorem sourceSpinorWeightedColor_gaugeTangent_component
    {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) (x : Boson N)
    (u : BosonLabel N) :
    (M.gaugeTangent x (sourceSpinorWeightedColor M w x)) u =
      -(∑ k : SpaceIndex,
        M.coordinateBracketAll x u.1 k u.2 *
          dotProduct w (M.gamma k *ᵥ w)) := by
  let v : SpaceIndex → ℝ :=
    fun k => dotProduct w (M.gamma k *ᵥ w)
  have hbracket (k : SpaceIndex) :
      (M.colorLie (spatialColor x k) (spatialColor x u.1)) u.2 =
        M.coordinateBracketAll x k u.1 u.2 := rfl
  calc
    (M.gaugeTangent x (sourceSpinorWeightedColor M w x)) u =
      ((sourceColorLieFirstLinear M (spatialColor x u.1))
        (∑ k : SpaceIndex, (v k) • spatialColor x k)) u.2 := rfl
    _ = (∑ k : SpaceIndex,
          (v k) • M.colorLie (spatialColor x k) (spatialColor x u.1)) u.2 := by
            rw [map_sum]
            simp only [map_smul]
            rfl
    _ = ∑ k : SpaceIndex,
          v k * M.coordinateBracketAll x k u.1 u.2 := by
            -- EuclideanSpace is PiLp, not an unbundled Pi function.
            -- Evaluate the sum through the canonical continuous linear
            -- coordinate projection, so linearity is justified directly.
            change (EuclideanSpace.proj (𝕜 := ℝ) u.2)
              (∑ k : SpaceIndex,
                v k • M.colorLie (spatialColor x k) (spatialColor x u.1)) = _
            rw [map_sum]
            simp only [map_smul, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro k _
            exact congrArg (fun a : ℝ => v k * a) (hbracket k)
    _ = -(∑ k : SpaceIndex,
          M.coordinateBracketAll x u.1 k u.2 * v k) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k _
            rw [M.coordinateBracketAll_skew x u.1 k u.2]
            ring

/-- The EXACT source W*K right-ordered mixed SmoothCore operator is
(-i) times the original source infinitesimal gauge-tangent vector
acting by the literal original coordinate derivatives. The color
direction depends on x but NO derivative ever acts on that weight:
this is explicitly RIGHT ordered. -/
theorem sourceSpinorRightOrderedMixed_eq_originalGaugeTangent_apply
    {N : ℕ} (M : AlgebraData N)
    (hgamma : M.gamma = originalGamma)
    (w : SpinIndex → ℝ)
    (f : SmoothCore N) (x : Boson N) :
    ((sourceSpinorRightOrderedMixed M w) f) x =
      ∑ u : BosonLabel N,
        ((-Complex.I) *
          (((M.gaugeTangent x
              (sourceSpinorWeightedColor M w x)) u : ℝ) : ℂ)) •
            ((sourceD u f) x) := by
  rw [sourceSpinorRightOrderedMixed_originalApply M hgamma w f x]
  apply Finset.sum_congr rfl
  intro u _
  rw [sourceSpinorWeightedColor_gaugeTangent_component M w x u]
  simp only [Complex.ofReal_neg]
  congr 1
  ring

#print axioms sourceColorLieFirstLinear
#print axioms sourceSpinorWeightedColor
#print axioms sourceSpinorWeightedColor_gaugeTangent_component
#print axioms sourceSpinorRightOrderedMixed_eq_originalGaugeTangent_apply
#check @sourceSpinorRightOrderedMixed_eq_originalGaugeTangent_apply
end
end FCP.BFSSSU2PhysicalDomainL6G5W
