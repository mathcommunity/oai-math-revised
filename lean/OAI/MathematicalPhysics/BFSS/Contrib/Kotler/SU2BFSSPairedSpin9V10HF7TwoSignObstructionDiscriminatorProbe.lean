import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF6SourceCommutatorObstructionProbe
import Mathlib.Algebra.Ring.Commute

/-!
K1D18V10H-F7 — two-sign determinant discriminator for the
exact genuine Mathlib source Spin9 representation.

F1 gave determinant square one, F4 established the genuine
source orientation normal subgroup H, F5 established an
explicit source determinant MonoidHom, and F6 proved that H
contains the genuine source commutator subgroup and equals
top CONDITIONAL on a supplied proof of source perfectness.

F7 characterizes a genuinely falsifiable alternative:
every determinant is +1 or -1; an actual negative-sign
source element is equivalent to a PROPER orientation subgroup
and would disprove source-group perfectness. No negative
element is produced; nor is absence of one asserted.

This is an algebraic two-sign boundary, NOT an appeal to
topological connectedness, a Spin48 lift, an implemented
Fock action or a physical BFSS prediction.

F7 is UNQUALIFIED until fresh pinned source, type,
and exact axiom CI passes.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Exactly the two real determinant signs are possible
for the original genuine source gamma16 representation. -/
theorem gammaDetDirectHom_eq_one_or_neg_one
    (g : spinGroup source9Quadratic) :
    gammaDetDirectHom g = 1 ∨ gammaDetDirectHom g = -1 := by
  exact (sq_eq_one_iff).mp (gammaDetDirectHom_sq g)

/-- A negative determinant witness lies outside the exact
accepted source Spin9 orientation subgroup, and conversely
an element outside it has determinant exactly -1. -/
theorem gammaDetDirectHom_eq_neg_one_iff_not_mem
    (g : spinGroup source9Quadratic) :
    gammaDetDirectHom g = -1 ↔
      g ∉ source9OrientationSubgroup := by
  constructor
  · intro hneg hmem
    have hpos :=
      (mem_source9OrientationSubgroup_iff_gammaDetDirectHom_one g).mp hmem
    have hcontr : (1 : ℝ) = -1 := hpos.symm.trans hneg
    norm_num at hcontr
  · intro hnot
    have hnotpos : gammaDetDirectHom g ≠ 1 := by
      intro hpos
      exact hnot
        ((mem_source9OrientationSubgroup_iff_gammaDetDirectHom_one g).mpr hpos)
    exact (gammaDetDirectHom_eq_one_or_neg_one g).resolve_left hnotpos

/-- The precise original source Spin9 orientation subgroup
is proper if and only if a real negative determinant witness
exists. No witness is supplied by this equivalence. -/
theorem source9OrientationSubgroup_ne_top_iff_exists_negative :
    source9OrientationSubgroup ≠ ⊤ ↔
      ∃ g : spinGroup source9Quadratic, gammaDetDirectHom g = -1 := by
  constructor
  · intro hne
    by_contra hn
    apply hne
    apply (Subgroup.eq_top_iff' _).mpr
    intro g
    by_contra hnot
    apply hn
    exact ⟨g, (gammaDetDirectHom_eq_neg_one_iff_not_mem g).mpr hnot⟩
  · rintro ⟨g, hneg⟩ htop
    have hnot :=
      (gammaDetDirectHom_eq_neg_one_iff_not_mem g).mp hneg
    apply hnot
    rw [htop]
    exact Subgroup.mem_top g

/-- A source-exact negative determinant witness, IF one
can be found, would refute source Spin9 perfectness.
This theorem neither asserts nor constructs such a g. -/
theorem not_source9_isPerfect_of_negative
    (g : spinGroup source9Quadratic)
    (hneg : gammaDetDirectHom g = -1) :
    ¬ Group.IsPerfect (spinGroup source9Quadratic) := by
  intro hp
  have htop := source9_orientation_eq_top_of_isPerfect hp
  have hnot :=
    (gammaDetDirectHom_eq_neg_one_iff_not_mem g).mp hneg
  apply hnot
  rw [htop]
  exact Subgroup.mem_top g

/-- A fully exact remaining obligation: the orientation
subgroup equals all genuine source Spin9 elements iff the
accepted determinant character equals +1 everywhere. -/
theorem source9OrientationSubgroup_eq_top_iff_all_positive :
    source9OrientationSubgroup = ⊤ ↔
      ∀ g : spinGroup source9Quadratic, gammaDetDirectHom g = 1 := by
  constructor
  · intro htop g
    apply (mem_source9OrientationSubgroup_iff_gammaDetDirectHom_one g).mp
    rw [htop]
    exact Subgroup.mem_top g
  · intro hpositive
    apply (Subgroup.eq_top_iff' _).mpr
    intro g
    exact (mem_source9OrientationSubgroup_iff_gammaDetDirectHom_one g).mpr
      (hpositive g)

#print axioms gammaDetDirectHom_eq_one_or_neg_one
#print axioms gammaDetDirectHom_eq_neg_one_iff_not_mem
#print axioms source9OrientationSubgroup_ne_top_iff_exists_negative
#print axioms not_source9_isPerfect_of_negative
#print axioms source9OrientationSubgroup_eq_top_iff_all_positive

end
end FCP.BFSSPairedSpin9DetFixture
