import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9ZeroDiagonalBracketsProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9FourIndexPairCoincidenceProbe

/-!
K1D18V8L — the five distinct-spatial-index patterns for the universal
four-index right-hand side, on the actual original paired-Fock 48 labels.

Each proof first reuses the source-exact strict-qualified V8I L bracket,
then reduces the literal V8J four-index RHS with named inequalities.
This bridges ONE shared endpoint in all four orientations, or four
different labels, without assuming the universal theorem or diagonal
raw K conventions. The full all-indices theorem remains separate.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- All four spatial labels are distinct: the exact four-index RHS vanishes. -/
theorem zeroDiagonalFourIndex_disjoint_case
    (r s t u : SpaceIndex) (hrs : r ≠ s) (htu : t ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t) (hsu : s ≠ u) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane t u -
      zeroDiagonalPairedPlane t u * zeroDiagonalPairedPlane r s =
    zeroDiagonalFourIndexRHS r s t u := by
  calc
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane t u -
        zeroDiagonalPairedPlane t u * zeroDiagonalPairedPlane r s = 0 :=
      zeroDiagonalPairedPlane_disjoint_bracket r s t u hrs htu hrt hru hst hsu
    _ = zeroDiagonalFourIndexRHS r s t u := by
      simp [zeroDiagonalFourIndexRHS, hrt, hru, hst, hsu]

/-- One common endpoint: the second first label equals the first second label. -/
theorem zeroDiagonalFourIndex_adjacent_case
    (r s t : SpaceIndex) (hrs : r ≠ s) (hst : s ≠ t) (hrt : r ≠ t) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane s t -
      zeroDiagonalPairedPlane s t * zeroDiagonalPairedPlane r s =
    zeroDiagonalFourIndexRHS r s s t := by
  calc
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane s t -
        zeroDiagonalPairedPlane s t * zeroDiagonalPairedPlane r s =
      -(zeroDiagonalPairedPlane r t + zeroDiagonalPairedPlane r t) :=
      zeroDiagonalPairedPlane_adjacent_bracket r s t hrs hst hrt
    _ = zeroDiagonalFourIndexRHS r s s t := by
      simp [zeroDiagonalFourIndexRHS, hrs, hst, hrt]

/-- One common right endpoint. -/
theorem zeroDiagonalFourIndex_shared_right_case
    (r s t : SpaceIndex) (hrs : r ≠ s) (hst : s ≠ t) (hrt : r ≠ t) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane t s -
      zeroDiagonalPairedPlane t s * zeroDiagonalPairedPlane r s =
    zeroDiagonalFourIndexRHS r s t s := by
  calc
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane t s -
        zeroDiagonalPairedPlane t s * zeroDiagonalPairedPlane r s =
      zeroDiagonalPairedPlane r t + zeroDiagonalPairedPlane r t :=
      zeroDiagonalPairedPlane_shared_right_bracket r s t hrs hst hrt
    _ = zeroDiagonalFourIndexRHS r s t s := by
      simp [zeroDiagonalFourIndexRHS, hrs, hst, hrt]

/-- One common left endpoint. -/
theorem zeroDiagonalFourIndex_shared_left_case
    (r s t : SpaceIndex) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane r t -
      zeroDiagonalPairedPlane r t * zeroDiagonalPairedPlane r s =
    zeroDiagonalFourIndexRHS r s r t := by
  calc
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane r t -
        zeroDiagonalPairedPlane r t * zeroDiagonalPairedPlane r s =
      zeroDiagonalPairedPlane s t + zeroDiagonalPairedPlane s t :=
      zeroDiagonalPairedPlane_shared_left_bracket r s t hrs hrt hst
    _ = zeroDiagonalFourIndexRHS r s r t := by
      simp [zeroDiagonalFourIndexRHS, hrt, hst, Ne.symm hrs]

/-- One common crossed endpoint. -/
theorem zeroDiagonalFourIndex_cross_right_case
    (r s t : SpaceIndex) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane t r -
      zeroDiagonalPairedPlane t r * zeroDiagonalPairedPlane r s =
    zeroDiagonalFourIndexRHS r s t r := by
  calc
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane t r -
        zeroDiagonalPairedPlane t r * zeroDiagonalPairedPlane r s =
      -(zeroDiagonalPairedPlane s t + zeroDiagonalPairedPlane s t) :=
      zeroDiagonalPairedPlane_cross_right_bracket r s t hrs hrt hst
    _ = zeroDiagonalFourIndexRHS r s t r := by
      simp [zeroDiagonalFourIndexRHS, hrt, hst, Ne.symm hrs]

#print axioms zeroDiagonalFourIndex_disjoint_case
#print axioms zeroDiagonalFourIndex_adjacent_case
#print axioms zeroDiagonalFourIndex_shared_right_case
#print axioms zeroDiagonalFourIndex_shared_left_case
#print axioms zeroDiagonalFourIndex_cross_right_case

end
end FCP.BFSSPairedSpin9Plane
