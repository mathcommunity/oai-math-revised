import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10PLipschitzGroupDetPositivityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF7TwoSignObstructionDiscriminatorProbe

/-!
K1D18V10H-F10Q — genuine source Spin9 determinant-one and orientation.

F7 gives exactly two possibilities for the original source gamma determinant
character; accepted F10P proves it is strictly positive for EVERY actual
source spinGroup element. This stage eliminates the negative alternative,
then specializes the previously accepted orientation-subgroup equivalence
and original paired 48-label determinant correspondence.

NO new source assumptions, replacement gamma tables, Fock basis changes,
group perfectness, connectivity, or topology. This does not construct
a Spin48 lift/cover, an actual Fock implementation, gauge invariance
or physical BFSS spectrum.

CANDIDATE until fresh pinned warning-as-error compilation and independent
three-declaration exact type / axiom audits pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Every genuine source Spin9 element has original real gamma
determinant +1: F7's two-sign exhaustive alternative and F10P's
strict positivity eliminate -1 without connectedness assumptions. -/
theorem gammaDetDirectHom_eq_one
    (g : spinGroup source9Quadratic) :
    gammaDetDirectHom g = 1 := by
  rcases gammaDetDirectHom_eq_one_or_neg_one g with hone | hneg
  · exact hone
  · have hpos : 0 < gammaDetDirectHom g :=
      gammaDetDirectHom_pos_of_source_spinGroup g
    rw [hneg] at hpos
    norm_num at hpos

/-- The previously accepted exact orientation subgroup is all
of genuine source Spin9, not just a conditional normal subgroup. -/
theorem source9OrientationSubgroup_eq_top :
    source9OrientationSubgroup = ⊤ := by
  apply source9OrientationSubgroup_eq_top_iff_all_positive.mpr
  intro g
  exact gammaDetDirectHom_eq_one g

/-- Every element of the accepted original G1A Fock-ordered paired
48-label algebraic orthogonal representation has determinant +1.
This is an exact determinant statement, not a Spin48 lift. -/
theorem source9SpinOriginalPaired48_det_one
    (g : spinGroup source9Quadratic) :
    (((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ)).det = 1 := by
  calc
    (((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ)).det =
        gammaDetDirectHom g :=
      (gammaDetDirectHom_eq_originalPaired48_det g).symm
    _ = 1 := gammaDetDirectHom_eq_one g

#print axioms gammaDetDirectHom_eq_one
#print axioms source9OrientationSubgroup_eq_top
#print axioms source9SpinOriginalPaired48_det_one

end
end FCP.BFSSPairedSpin9DetFixture
