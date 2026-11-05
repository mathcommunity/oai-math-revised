import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9ZeroDiagonalInterfaceProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9AdjacentLieBracketProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9DisjointLieBracketProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9SharedEndBracketProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9SharedLeftBracketProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9CrossRightBracketProbe

/-!
K1D18V8I — exact source-native zero-diagonal L bracket transport.

Five independent, exact-type bridges transport the already accepted original
paired-Fock K bracket lemmas to L(r,s) = if r=s then 0 else K(r,s)
*only for their strictly specified distinct-index cases*.

They do not assume that raw K(r,r) is zero. They do not establish a blanket
all-index Lie bracket or integrate a global Spin(9) group action.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

theorem zeroDiagonalPairedPlane_adjacent_bracket
    (r s t : SpaceIndex) (hrs : r ≠ s) (hst : s ≠ t) (hrt : r ≠ t) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane s t -
        zeroDiagonalPairedPlane s t * zeroDiagonalPairedPlane r s =
      -(zeroDiagonalPairedPlane r t + zeroDiagonalPairedPlane r t) := by
  simpa only [zeroDiagonalPairedPlane_of_ne r s hrs,
    zeroDiagonalPairedPlane_of_ne s t hst,
    zeroDiagonalPairedPlane_of_ne r t hrt] using
    (originalPairedPlane_adjacent_bracket r s t hrs hst hrt)

theorem zeroDiagonalPairedPlane_disjoint_bracket
    (r s t u : SpaceIndex) (hrs : r ≠ s) (htu : t ≠ u)
    (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t) (hsu : s ≠ u) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane t u -
        zeroDiagonalPairedPlane t u * zeroDiagonalPairedPlane r s = 0 := by
  simpa only [zeroDiagonalPairedPlane_of_ne r s hrs,
    zeroDiagonalPairedPlane_of_ne t u htu] using
    (originalPairedPlane_disjoint_bracket r s t u hrs htu hrt hru hst hsu)

theorem zeroDiagonalPairedPlane_shared_right_bracket
    (r s t : SpaceIndex) (hrs : r ≠ s) (hst : s ≠ t) (hrt : r ≠ t) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane t s -
        zeroDiagonalPairedPlane t s * zeroDiagonalPairedPlane r s =
      zeroDiagonalPairedPlane r t + zeroDiagonalPairedPlane r t := by
  simpa only [zeroDiagonalPairedPlane_of_ne r s hrs,
    zeroDiagonalPairedPlane_of_ne t s (Ne.symm hst),
    zeroDiagonalPairedPlane_of_ne r t hrt] using
    (originalPairedPlane_shared_right_bracket r s t hrs hst hrt)

theorem zeroDiagonalPairedPlane_shared_left_bracket
    (r s t : SpaceIndex) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane r t -
        zeroDiagonalPairedPlane r t * zeroDiagonalPairedPlane r s =
      zeroDiagonalPairedPlane s t + zeroDiagonalPairedPlane s t := by
  simpa only [zeroDiagonalPairedPlane_of_ne r s hrs,
    zeroDiagonalPairedPlane_of_ne r t hrt,
    zeroDiagonalPairedPlane_of_ne s t hst] using
    (originalPairedPlane_shared_left_bracket r s t hrs hrt hst)

theorem zeroDiagonalPairedPlane_cross_right_bracket
    (r s t : SpaceIndex) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane t r -
        zeroDiagonalPairedPlane t r * zeroDiagonalPairedPlane r s =
      -(zeroDiagonalPairedPlane s t + zeroDiagonalPairedPlane s t) := by
  simpa only [zeroDiagonalPairedPlane_of_ne r s hrs,
    zeroDiagonalPairedPlane_of_ne t r (Ne.symm hrt),
    zeroDiagonalPairedPlane_of_ne s t hst] using
    (originalPairedPlane_cross_right_bracket r s t hrs hrt hst)

#print axioms zeroDiagonalPairedPlane_adjacent_bracket
#print axioms zeroDiagonalPairedPlane_disjoint_bracket
#print axioms zeroDiagonalPairedPlane_shared_right_bracket
#print axioms zeroDiagonalPairedPlane_shared_left_bracket
#print axioms zeroDiagonalPairedPlane_cross_right_bracket

end
end FCP.BFSSPairedSpin9Plane
