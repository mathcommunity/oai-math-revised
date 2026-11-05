import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10NOriginalGammaPositiveDeterminantProbe

/-!
K1D18V10H-F10O — exact source Clifford-unit generator DET POSITIVITY.

F10N is independently qualified: det gamma(v) = Q(v)^8 for every
original 9-vector, including zero, and exact evaluation on actual
Clifford UNIT vector generators. A genuine unit cannot map to zero
under the ambient monoid determinant character, since its image
has a multiplicative inverse in the sense f(u)*f(u⁻¹) = 1.

This bounded stage proves:
1. the genuine determinant monoid hom never vanishes on ANY
   unit of the source Clifford algebra;
2. a unit whose underlying Clifford value is an original source
   generator ι Q v has STRICTLY POSITIVE determinant;
3. the monoid determinant image of u⁻¹ is strictly positive when
   that of u is positive (no assumed group-valued hom).

The pinned source Mathlib SpinGroup defines the Lipschitz subgroup
as Subgroup.closure of exactly those unit vector generators.
The NEXT stage will use closure induction to propagate these
positive values to all Lipschitz units, then the accepted Spin9
determinant-square-one bridge to prove the source Spin9 character.
NONE of that closure/global result is claimed in this module.

No private gamma table, basis permutation, bypassed linters,
sorry, native_decide, new axiom or resource-limit adjustment.
F10O is unqualified until strict four? THREE exact type/axiom checks pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- The existing actual source Clifford UNIT determinant monoid hom
has a nonzero value on EVERY unit, independent of gamma generators. -/
theorem source9CliffordUnitsGammaDetHom_ne_zero
    (u : (CliffordAlgebra source9Quadratic)ˣ) :
    source9CliffordUnitsGammaDetHom u ≠ 0 := by
  have hmul :
      source9CliffordUnitsGammaDetHom u *
        source9CliffordUnitsGammaDetHom u⁻¹ = 1 := by
    calc
      source9CliffordUnitsGammaDetHom u *
          source9CliffordUnitsGammaDetHom u⁻¹ =
        source9CliffordUnitsGammaDetHom (u * u⁻¹) :=
          (map_mul source9CliffordUnitsGammaDetHom u u⁻¹).symm
      _ = 1 := by simp
  intro hz
  rw [hz, zero_mul] at hmul
  norm_num at hmul

/-- Any unit representing the exact original source Clifford vector
has STRICTLY POSITIVE determinant, using the qualified F10N formula
and nonvanishing of the image of an actual unit. -/
theorem source9CliffordUnitsGammaDetHom_pos_generator
    (u : (CliffordAlgebra source9Quadratic)ˣ)
    (v : SpaceIndex → ℝ)
    (hvec : (u : CliffordAlgebra source9Quadratic) =
      CliffordAlgebra.ι source9Quadratic v) :
    0 < source9CliffordUnitsGammaDetHom u := by
  have hformula :=
    source9CliffordUnitsGammaDetHom_generator_positive_branch u v hvec
  have hne : (source9Quadratic v) ^ 8 ≠ 0 := by
    rw [← hformula]
    exact source9CliffordUnitsGammaDetHom_ne_zero u
  rw [hformula]
  rcases lt_or_eq_of_le (pow_nonneg (source9Quadratic_nonneg v) 8) with hp | hz
  · exact hp
  · exact (hne hz.symm).elim

/-- Positivity of the original Clifford-unit determinant character
is closed under inverses, without claiming it maps to ℝˣ. -/
theorem source9CliffordUnitsGammaDetHom_pos_inv_of_pos
    (u : (CliffordAlgebra source9Quadratic)ˣ)
    (hu : 0 < source9CliffordUnitsGammaDetHom u) :
    0 < source9CliffordUnitsGammaDetHom u⁻¹ := by
  have hmul :
      source9CliffordUnitsGammaDetHom u *
        source9CliffordUnitsGammaDetHom u⁻¹ = 1 := by
    calc
      source9CliffordUnitsGammaDetHom u *
          source9CliffordUnitsGammaDetHom u⁻¹ =
        source9CliffordUnitsGammaDetHom (u * u⁻¹) :=
          (map_mul source9CliffordUnitsGammaDetHom u u⁻¹).symm
      _ = 1 := by simp
  by_contra hnot
  have hle : source9CliffordUnitsGammaDetHom u⁻¹ ≤ 0 :=
    le_of_not_gt hnot
  have hprod : source9CliffordUnitsGammaDetHom u *
      source9CliffordUnitsGammaDetHom u⁻¹ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hu) hle
  rw [hmul] at hprod
  norm_num at hprod

#print axioms source9CliffordUnitsGammaDetHom_ne_zero
#print axioms source9CliffordUnitsGammaDetHom_pos_generator
#print axioms source9CliffordUnitsGammaDetHom_pos_inv_of_pos

end
end FCP.BFSSPairedSpin9DetFixture
