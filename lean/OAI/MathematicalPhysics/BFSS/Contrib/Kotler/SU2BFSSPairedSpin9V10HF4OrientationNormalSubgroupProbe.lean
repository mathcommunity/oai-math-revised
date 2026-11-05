import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF3SourceSquareOrientationProbe
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
K1D18V10H-F4 — the exact source Spin(9)
orientation-preserving subgroup and its normality.

Only previously qualified source F3/F2/F1 and original
Spin9/O16/O(original paired48) sources are imported.
The failing determinant-character source remains EXCLUDED.

Construct the determinant +1 preimage directly as a genuine
Subgroup of the exact pinned spinGroup source9Quadratic;
show that all source squares belong to it, and that it is
normal by the accepted matrix determinant product rule.
No MonoidHom composition or expensive character unfolding.
Its equality with top is an OPEN mathematical obligation.

F4 is a strictly UNQUALIFIED source candidate until CI.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Exact determinant of identity for the qualified global
source Spin9 gamma orthogonal group homomorphism. -/
theorem gammaDet_one :
    (((source9SpinGammaOrthogonalHom
      (1 : spinGroup source9Quadratic)) : GammaMatrix).det) = 1 := by
  have h :=
    congrArg
      (fun A : Matrix.orthogonalGroup SpinIndex ℝ => (A : GammaMatrix))
      (map_one source9SpinGammaOrthogonalHom)
  have hd := congrArg Matrix.det h
  simpa only [Submonoid.coe_one, Matrix.det_one] using hd

/-- Source EXACT Spin9 orientation-preserving subgroup,
using a scalar equality on the original qualified 16-real
gamma representation, NOT an unqualified determinant
MonoidHom or a surjectivity assumption. -/
noncomputable def source9OrientationSubgroup :
    Subgroup (spinGroup source9Quadratic) where
  carrier := {g | (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) = 1}
  one_mem' := by
    exact gammaDet_one
  mul_mem' := by
    intro g h hg hh
    change (((source9SpinGammaOrthogonalHom (g * h)) : GammaMatrix).det) = 1
    change (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) = 1 at hg
    change (((source9SpinGammaOrthogonalHom h) : GammaMatrix).det) = 1 at hh
    rw [gammaDet_mul g h, hg, hh, one_mul]
  inv_mem' := by
    intro g hg
    change (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) = 1 at hg
    change (((source9SpinGammaOrthogonalHom g⁻¹) : GammaMatrix).det) = 1
    have hprod := gammaDet_mul g g⁻¹
    rw [mul_inv_cancel, gammaDet_one] at hprod
    rw [hg, one_mul] at hprod
    exact hprod.symm

/-- Genuine original paired-Fock 48-label SO membership is
EXACTLY membership in this source Spin9 subgroup. -/
theorem mem_source9OrientationSubgroup_iff_pairedSO
    (g : spinGroup source9Quadratic) :
    g ∈ source9OrientationSubgroup ↔
      ((source9SpinOriginalPaired48OrthogonalHom g) :
        Matrix Source48Label Source48Label ℝ) ∈
        Matrix.specialOrthogonalGroup Source48Label ℝ := by
  change (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) = 1 ↔ _
  exact (pairedSO_iff_gammaDetOne g).symm

/-- The exact source Spin9 orientation subgroup contains
every algebraic group square. No claim every g is a square. -/
theorem source9OrientationSubgroup_sq_mem
    (g : spinGroup source9Quadratic) :
    g * g ∈ source9OrientationSubgroup := by
  change (((source9SpinGammaOrthogonalHom (g * g)) : GammaMatrix).det) = 1
  exact gammaDet_square_one g

/-- The determinant-one subgroup is normal under conjugacy
by any GENUINE source Spin9 element. This uses only
det(g*n*g⁻¹) = det(g) det(n) det(g⁻¹) and det(n)=1.
In particular, it does not establish subgroup = top. -/
instance source9OrientationSubgroup_normal :
    Subgroup.Normal source9OrientationSubgroup where
  conj_mem := by
    intro n hn g
    change (((source9SpinGammaOrthogonalHom n) : GammaMatrix).det) = 1 at hn
    change (((source9SpinGammaOrthogonalHom (g * n * g⁻¹)) :
      GammaMatrix).det) = 1
    have hginv :
        (((source9SpinGammaOrthogonalHom g) : GammaMatrix).det) *
          (((source9SpinGammaOrthogonalHom g⁻¹) : GammaMatrix).det) = 1 := by
      have h := gammaDet_mul g g⁻¹
      rw [mul_inv_cancel, gammaDet_one] at h
      exact h.symm
    rw [gammaDet_mul (g * n) g⁻¹, gammaDet_mul g n, hn, mul_one]
    exact hginv

#print axioms gammaDet_one
#print axioms source9OrientationSubgroup
#print axioms mem_source9OrientationSubgroup_iff_pairedSO
#print axioms source9OrientationSubgroup_sq_mem
#print axioms source9OrientationSubgroup_normal

end
end FCP.BFSSPairedSpin9DetFixture
