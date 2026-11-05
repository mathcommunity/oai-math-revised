import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9FourIndexDistinctCasesProbe

/-!
K1D18V8M — original paired-Fock 48-real Spin(9) Lie-bracket
all-indices case assembly.

V8J proved both diagonal input cases; V8K proved identical and reversed
non-diagonal pairs; V8L proved four-distinct and all four exactly-one
shared-index orientations. This SINGLE new theorem assembles those
source-exact Lean facts with six typed by_cases, without changing the
underlying gamma matrices or replacing original paired Source48Label.

This identity is an all-indices Matrix bracket, NOT a proved global Spin(9)
group homomorphism, Fock operator implementation, or physical BFSS theorem.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- Universal exact four-index Lie bracket for the source-original 48-real
zero-diagonal matrices L, including *all* index coincidences. -/
theorem zeroDiagonalFourIndex_universal_bracket (r s t u : SpaceIndex) :
    zeroDiagonalPairedPlane r s * zeroDiagonalPairedPlane t u -
      zeroDiagonalPairedPlane t u * zeroDiagonalPairedPlane r s =
    zeroDiagonalFourIndexRHS r s t u := by
  by_cases hrs : r = s
  · subst s
    exact zeroDiagonalFourIndex_left_self_bracket r t u
  · by_cases htu : t = u
    · subst u
      exact zeroDiagonalFourIndex_right_self_bracket r s t
    · by_cases hrt : r = t
      · subst t
        by_cases hsu : s = u
        · subst u
          exact zeroDiagonalFourIndex_same_pair_bracket r s hrs
        · exact zeroDiagonalFourIndex_shared_left_case r s u hrs htu hsu
      · by_cases hru : r = u
        · subst u
          by_cases hst : s = t
          · subst t
            exact zeroDiagonalFourIndex_reverse_pair_bracket r s hrs
          · exact zeroDiagonalFourIndex_cross_right_case r s t hrs hrt hst
        · by_cases hst : s = t
          · subst t
            exact zeroDiagonalFourIndex_adjacent_case r s u hrs htu hru
          · by_cases hsu : s = u
            · subst u
              exact zeroDiagonalFourIndex_shared_right_case r s t hrs hst hrt
            · exact zeroDiagonalFourIndex_disjoint_case
                r s t u hrs htu hrt hru hst hsu

#print axioms zeroDiagonalFourIndex_universal_bracket

end
end FCP.BFSSPairedSpin9Plane
