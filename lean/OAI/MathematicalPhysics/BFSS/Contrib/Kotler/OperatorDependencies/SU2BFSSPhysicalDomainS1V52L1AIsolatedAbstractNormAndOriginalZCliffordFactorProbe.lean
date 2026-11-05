import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52S2Original48CliffordQuaternionEvennessProbe

/-!
S1V52-L1A ISOLATED STRICT CANDIDATE: preserve two algebraic roots
already locally kernel-clean on red L1 Gates 1–4.
The real generic quadratic norm does not assert the original source
Z-plane unit-vector norm (that is still an unqualified L1B obligation).
The exact original +i Z Clifford two-ι factor uses true source Q.
No original Lipschitz/Spin membership, sixteen-block lift, or continuity
is proved by either theorem alone.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000

namespace FCP.BFSSS1V52L1A
noncomputable section
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V6
open FCP.BFSSS1V52A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Generic real quadratic norm calculation: for *any* quadratic
form on *any* real vector space, a normalized orthogonal pair and a
circle pair of scalar coefficients yield another unit vector.
Keeping map_add/polar lemmas abstract avoids evaluating the actual
48-Majorana indexing and weightedSumSquares in elaboration. -/
theorem orthogonalUnitLinearCombination_norm
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : QuadraticForm ℝ V) (a b : V) (c s : ℝ)
    (ha : q a = 1) (hb : q b = 1)
    (hab : q.IsOrtho a b) (hcs : c*c+s*s=1) :
    q (c • a - s • b) = 1 := by
  have hpolar : QuadraticMap.polar q a b = 0 := hab.polar_eq_zero
  calc
    q (c • a - s • b) =
        q (c • a + (-s) • b) := by
          simp only [neg_smul, sub_eq_add_neg]
    _ = q (c • a) + q ((-s) • b) +
        QuadraticMap.polar q (c • a) ((-s) • b) :=
      QuadraticMap.map_add q _ _
    _ = 1 := by
      rw [QuadraticMap.map_smul, QuadraticMap.map_smul,
        QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_right, hpolar]
      simp only [ha, hb, smul_eq_mul]
      nlinarith [hcs]

/-- A normalized source Z-plane rotor equals exactly the product
of two ORIGINAL Clifford vector generators, with the +i sign:
(ι(c a - s b)) (ι a) = c • 1 + s • (ι a)(ι b). -/
theorem sourceZPlane_twoVector_factor
    (α : RealSpinBlock) (c s : ℝ) :
    CliffordAlgebra.ι Q
      (c • sourceBlockColorAxis α 0 -
       s • sourceBlockColorAxis α 1) *
      CliffordAlgebra.ι Q (sourceBlockColorAxis α 0) =
      c • (1 : C) + s • sourceZBivector α := by
  let a : Source48Vector := sourceBlockColorAxis α 0
  let b : Source48Vector := sourceBlockColorAxis α 1
  have haa : CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q a = 1 :=
    sourceAxis_square α 0
  have hba : CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q a =
      -(CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) :=
    sourceAxis_anticomm α 1 0 (by decide)
  change CliffordAlgebra.ι Q (c • a - s • b) *
      CliffordAlgebra.ι Q a =
      c • (1 : C) +
        s • (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b)
  calc
    CliffordAlgebra.ι Q (c • a - s • b) *
        CliffordAlgebra.ι Q a =
        (c • CliffordAlgebra.ι Q a -
          s • CliffordAlgebra.ι Q b) * CliffordAlgebra.ι Q a := by
        rw [map_sub, map_smul, map_smul]
    _ = c • (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q a) -
        s • (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q a) := by
        simp only [sub_mul, smul_mul_assoc]
    _ = c • (1 : C) +
        s • (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) := by
        rw [haa, hba]
        simp only [smul_neg, sub_neg_eq_add]

#print axioms orthogonalUnitLinearCombination_norm
#print axioms sourceZPlane_twoVector_factor
end
end FCP.BFSSS1V52L1A
