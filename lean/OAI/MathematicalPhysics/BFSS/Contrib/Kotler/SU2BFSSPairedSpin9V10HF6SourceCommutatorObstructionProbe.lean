import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF5TypedDirectDeterminantCharacterProbe
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Commutator.Basic

/-!
K1D18V10H-F6 — source-exact commutator obstruction to
orientation and carefully CONDITIONAL perfectness bridge.

The verified F5 determinant is a direct MonoidHom
from genuine source Spin9 into the commutative
multiplicative monoid of the real numbers. Although
the codomain is not a group, the group inverse
identity gives chi(g) * chi(g^-1) = 1.
By multiplicativity and real commutativity every
genuine source commutator maps to +1.

The next algebraic result is not merely that all
squares have determinant +1: the entire source
commutator subgroup lies in the previously accepted
orientation-preserving normal subgroup.

An explicitly SUPPLIED proof of Group.IsPerfect for
the genuine source Spin9 group would then imply
that this orientation subgroup is top and the actual
paired-Fock 48 image is globally SO48. Mathlib's
general IsPerfect API alone does NOT provide such
a source-specific proof. We do NOT create an
IsPerfect instance or assert source perfectness.

No continuity, Spin48 lift, Fock unitary, or
BFSS physical claims are implied.

F6 CANDIDATE until fresh source and axiom CI passes.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix
open scoped commutatorElement

/-- Inverses in genuine source Spin9 yield inverse
determinants without assuming ℝ is a group. -/
theorem gammaDetDirectHom_inv_mul
    (g : spinGroup source9Quadratic) :
    gammaDetDirectHom g * gammaDetDirectHom g⁻¹ = 1 := by
  have h := map_mul gammaDetDirectHom g g⁻¹
  rw [mul_inv_cancel, map_one] at h
  exact h.symm

/-- Every genuine source Spin9 commutator has
determinant +1 in the original real gamma16 action.
Use the accepted typed direct character; do not
unfold nested original source homomorphisms. -/
theorem gammaDetDirectHom_commutator
    (g h : spinGroup source9Quadratic) :
    gammaDetDirectHom ⁅g, h⁆ = 1 := by
  have hproduct :
      gammaDetDirectHom ⁅g, h⁆ =
        gammaDetDirectHom g * gammaDetDirectHom h *
          gammaDetDirectHom g⁻¹ * gammaDetDirectHom h⁻¹ := by
    rw [commutatorElement_def]
    simp only [map_mul]
  calc
    gammaDetDirectHom ⁅g, h⁆ =
        gammaDetDirectHom g * gammaDetDirectHom h *
          gammaDetDirectHom g⁻¹ * gammaDetDirectHom h⁻¹ := hproduct
    _ = (gammaDetDirectHom g * gammaDetDirectHom g⁻¹) *
          (gammaDetDirectHom h * gammaDetDirectHom h⁻¹) := by ring
    _ = 1 := by
      rw [gammaDetDirectHom_inv_mul g, gammaDetDirectHom_inv_mul h, one_mul]

/-- The EXACT derived/commutator subgroup of original
Mathlib spinGroup source9Quadratic is contained in the
verified normal determinant-one subgroup. -/
theorem source9_commutator_le_orientation :
    commutator (spinGroup source9Quadratic) ≤
      source9OrientationSubgroup := by
  rw [commutator_def]
  apply (Subgroup.commutator_le).2
  intro g _ h _
  exact (mem_source9OrientationSubgroup_iff_gammaDetDirectHom_one
    ⁅g, h⁆).2 (gammaDetDirectHom_commutator g h)

/-- CONDITIONAL: if and only if the caller supplies an
actual proof that the original source Spin9 group is
perfect, the proved commutator inclusion yields
global orientation subgroup = top.
No such proof is constructed by this theorem. -/
theorem source9_orientation_eq_top_of_isPerfect
    (hperfect : Group.IsPerfect (spinGroup source9Quadratic)) :
    source9OrientationSubgroup = ⊤ := by
  apply le_antisymm le_top
  rw [← hperfect.commutator_eq_top]
  exact source9_commutator_le_orientation

/-- CONDITIONAL original paired-Fock 48 SO membership:
requires the SAME explicitly supplied source-group
perfectness proof. Does not produce it. -/
theorem originalPaired48_mem_SO_of_isPerfect
    (hperfect : Group.IsPerfect (spinGroup source9Quadratic))
    (g : spinGroup source9Quadratic) :
    ((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ) ∈
      Matrix.specialOrthogonalGroup Source48Label ℝ := by
  have htop := source9_orientation_eq_top_of_isPerfect hperfect
  have hg : g ∈ source9OrientationSubgroup := by
    rw [htop]
    trivial
  exact (mem_source9OrientationSubgroup_iff_pairedSO g).1 hg

#print axioms gammaDetDirectHom_inv_mul
#print axioms gammaDetDirectHom_commutator
#print axioms source9_commutator_le_orientation
#print axioms source9_orientation_eq_top_of_isPerfect
#print axioms originalPaired48_mem_SO_of_isPerfect

end
end FCP.BFSSPairedSpin9DetFixture
