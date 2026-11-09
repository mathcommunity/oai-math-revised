import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AVOriginalGammaCoordinateLinearMapSkewImage
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9CoordinateUniversalBracketProbe

/-!
K1D18V10H-F10AW — original-gamma coordinate-plane
generator-pair bracket compatibility.

This gate proves bracket preservation for every pair of
source-native coordinate planes under the original-gamma
coefficient LinearMap.

The proof composes:
* F10AV's exact coordinate-plane evaluation;
* F10AU's exhaustive native so(16) oriented-pair bracket;
* the native source four-index coordinate-plane bracket.

F10AU's native LieSubalgebra bracket is transported to the
GammaMatrix carrier before the source coefficient map is
compared. The source and target four-index expressions retain
the same priority-ordered dependent-if collision semantics.
All case splits are performed on the unchanged source labels;
no substitution-based case table is maintained separately.

The factor is forced: (1/2)(1/2) times the gamma-pair
commutator coefficient 2 gives 1/2, exactly the coefficient
of the source coordinate-plane bracket under rho.

This proves generator-pair bracket compatibility only.
It does NOT yet prove arbitrary-skew bracket preservation,
a typed so(9) -> so(16) LieHom, global Spin(9) integration,
a Spin(48) lift or covering, an original Fock action,
gauge/physical-domain compatibility, or BFSS spectral
existence.

No replacement gamma basis, source-label permutation,
guessed normalization, axiom, admission, linter suppression,
or increased proof limit is permitted.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open FCP.BFSSPairedSpin9Plane
open OAI.BFSSQuantum
open Matrix

/-- The original-gamma coefficient LinearMap preserves the
commutator of every pair of source-native coordinate planes.
All diagonal and index-coincidence cases are included. -/
theorem coordinateToOriginalGammaLinearMap_coordinatePlane_bracket
    (r s t u : SpaceIndex) :
    coordinateToOriginalGammaLinearMap
        (coordinatePlane9 r s * coordinatePlane9 t u -
          coordinatePlane9 t u * coordinatePlane9 r s) =
      coordinateToOriginalGammaLinearMap (coordinatePlane9 r s) *
          coordinateToOriginalGammaLinearMap (coordinatePlane9 t u) -
        coordinateToOriginalGammaLinearMap (coordinatePlane9 t u) *
          coordinateToOriginalGammaLinearMap (coordinatePlane9 r s) := by
  by_cases hrs : r = s
  · subst s
    simp [coordinatePlane9_self]
  · by_cases htu : t = u
    · subst u
      simp [coordinatePlane9_self]
    · rw [coordinatePlane9_universal_four_index_bracket]
      simp only [coordinateToOriginalGammaLinearMap_coordinatePlane,
        dite_eq_right hrs, dite_eq_right htu]
      have hpair :=
        source9OriginalGamma_exhaustive_oriented_pair_native_so_bracket
          r s t u hrs htu
      have hmatrix :
          (gamma r * gamma s) * (gamma t * gamma u) -
            (gamma t * gamma u) * (gamma r * gamma s) =
          if hac : r = t then
            if hbd : s = u then
              (0 : GammaMatrix)
            else
              -((2 : ℝ) • (gamma s * gamma u))
          else if hbc : s = t then
            if had : r = u then
              (0 : GammaMatrix)
            else
              (2 : ℝ) • (gamma r * gamma u)
          else if _hbd : s = u then
            -((2 : ℝ) • (gamma r * gamma t))
          else if _had : r = u then
            (2 : ℝ) • (gamma s * gamma t)
          else
            (0 : GammaMatrix) := by
        have h := congrArg
          (fun z : LieAlgebra.Orthogonal.so SpinIndex ℝ => (z : GammaMatrix))
          hpair
        simp only [LieSubalgebra.coe_bracket,
          LieRing.of_associative_ring_bracket] at h
        split_ifs at h ⊢ <;>
          simpa [source9OriginalGammaDistinctPairInSo] using h
      have hhalf :
          ((1 / 2 : ℝ) • (gamma r * gamma s)) *
              ((1 / 2 : ℝ) • (gamma t * gamma u)) -
            ((1 / 2 : ℝ) • (gamma t * gamma u)) *
              ((1 / 2 : ℝ) • (gamma r * gamma s)) =
          (1 / 4 : ℝ) •
            ((gamma r * gamma s) * (gamma t * gamma u) -
              (gamma t * gamma u) * (gamma r * gamma s)) := by
        calc
          _ =
              (1 / 2 : ℝ) •
                  ((1 / 2 : ℝ) •
                    ((gamma r * gamma s) * (gamma t * gamma u))) -
                (1 / 2 : ℝ) •
                  ((1 / 2 : ℝ) •
                    ((gamma t * gamma u) * (gamma r * gamma s))) := by
            rw [smul_mul_assoc, mul_smul_comm,
              smul_mul_assoc, mul_smul_comm]
          _ =
              (1 / 4 : ℝ) •
                ((gamma r * gamma s) * (gamma t * gamma u) -
                  (gamma t * gamma u) * (gamma r * gamma s)) := by
            rw [smul_smul, smul_smul, ← smul_sub]
            norm_num
      have hscaled :=
        congrArg (fun X : GammaMatrix => (1 / 4 : ℝ) • X) hmatrix
      rw [hhalf, hscaled]
      have map_conditional (p : Prop) [Decidable p]
          (A : Matrix SpaceIndex SpaceIndex ℝ) :
          coordinateToOriginalGammaLinearMap (if p then A else 0) =
            if p then coordinateToOriginalGammaLinearMap A else 0 := by
        by_cases hp : p <;> simp [hp]
      simp only [coordinateFourIndexRHS, map_neg, map_add, map_sub,
        map_conditional, coordinateToOriginalGammaLinearMap_coordinatePlane]
      have no_su_ru (hsu : s = u) (hru : r = u) : False :=
        hrs (hru.trans hsu.symm)
      have no_st_rt (hst : s = t) (hrt : r = t) : False :=
        hrs (hrt.trans hst.symm)
      have no_rt_ru (hrt : r = t) (hru : r = u) : False :=
        htu (hrt.symm.trans hru)
      split_ifs <;>
        first
        | exfalso
          solve_by_elim [no_su_ru, no_st_rt, no_rt_ru]
        | (simp_all <;> norm_num [smul_smul])

#print axioms coordinateToOriginalGammaLinearMap_coordinatePlane_bracket

end
end FCP.BFSSPairedSpin9Clifford
