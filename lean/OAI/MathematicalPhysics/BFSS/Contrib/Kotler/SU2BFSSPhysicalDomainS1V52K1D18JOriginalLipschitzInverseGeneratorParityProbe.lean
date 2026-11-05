import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18IOriginalLipschitzGeneratorParityProbe

/-!
K1D18J — actual Lipschitz inverse-generator boundary of determinant
and grade-sign agreement, using original source48Quadratic, actual
Clifford ι, real-linear determinant character and the pinned Clifford
involute map.

Only inverse ORIGINAL generator units. No general closure induction,
Spin-even determinant theorem, SO48, covering, global Spin9, or BFSS
spectral existence claim. Candidate until strict source compiler and
declaration-level axiom audit.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18J
noncomputable section

open FCP.BFSSS1V0
open CliffordAlgebra

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev L := lipschitzGroup Q
private abbrev generator
    (a : Source48Vector) [Invertible (CliffordAlgebra.ι Q a)] : L :=
  FCP.BFSSS1V52K1D18I.originalSourceGeneratorLipschitzUnit a

/-- The real unit determinant character of the actual inverse
original Clifford-vector generator equals -1. No arbitrary source
Spin word factorization is introduced. -/
theorem originalSourceGeneratorInverse_det_neg_one
    (a : Source48Vector) [Invertible (CliffordAlgebra.ι Q a)] :
    ((FCP.BFSSS1V52K1D18H.originalSourceLipschitzDeterminantCharacter
      (generator a)⁻¹ : ℝˣ) : ℝ) = -1 := by
  rw [map_inv, Units.val_inv_eq_inv_val,
    FCP.BFSSS1V52K1D18I.originalSourceGeneratorLipschitzDeterminant_neg_one]
  norm_num

/-- The genuine source Clifford grade involution negates the inverse
of an actual original invertible Clifford-generator unit. We use
actual unit inversion, multiplicativity of involution, and the exact original generator
grade sign, without assuming an even Spin element. -/
theorem originalSourceGeneratorInverse_involute_neg
    (a : Source48Vector) [Invertible (CliffordAlgebra.ι Q a)] :
    CliffordAlgebra.involute
      ((((generator a)⁻¹ : L) : Cˣ) : C) =
      -((((generator a)⁻¹ : L) : Cˣ) : C) := by
  let u : Cˣ := (generator a : Cˣ)
  have hu : CliffordAlgebra.involute (u : C) = -(u : C) :=
    FCP.BFSSS1V52K1D18I.originalSourceGeneratorLipschitzUnit_involute_neg a
  change CliffordAlgebra.involute ((u⁻¹ : Cˣ) : C) =
    -((u⁻¹ : Cˣ) : C)
  have hinv_mul :
      CliffordAlgebra.involute ((u⁻¹ : Cˣ) : C) *
        CliffordAlgebra.involute (u : C) = (1 : C) := by
    rw [← map_mul]
    simp
  have hinv_neg :
      CliffordAlgebra.involute ((u⁻¹ : Cˣ) : C) *
        (-(u : C)) = (1 : C) := by
    rw [← hu]
    exact hinv_mul
  have hinv_mul_unit :
      CliffordAlgebra.involute ((u⁻¹ : Cˣ) : C) *
        (u : C) = (-1 : C) := by
    calc
      _ = -(CliffordAlgebra.involute ((u⁻¹ : Cˣ) : C) *
          (-(u : C))) := by simp
      _ = -(1 : C) := by rw [hinv_neg]
  calc
    CliffordAlgebra.involute ((u⁻¹ : Cˣ) : C) =
        (CliffordAlgebra.involute ((u⁻¹ : Cˣ) : C) *
          (u : C)) * ((u⁻¹ : Cˣ) : C) := by
            rw [mul_assoc, Units.mul_inv, mul_one]
    _ = (-1 : C) * ((u⁻¹ : Cˣ) : C) := by rw [hinv_mul_unit]
    _ = -((u⁻¹ : Cˣ) : C) := by simp

/-- Grade sign and the genuine source Lipschitz determinant character
AGREE on inverse generator units. This is a quantified mathematical
identity on the actual Clifford algebra; extending it to arbitrary
products and the entire subgroup closure remains separate. -/
theorem originalSourceGeneratorInverse_grade_det_agreement
    (a : Source48Vector) [Invertible (CliffordAlgebra.ι Q a)] :
    CliffordAlgebra.involute
      ((((generator a)⁻¹ : L) : Cˣ) : C) =
    (((FCP.BFSSS1V52K1D18H.originalSourceLipschitzDeterminantCharacter
      (generator a)⁻¹ : ℝˣ) : ℝ)) •
      ((((generator a)⁻¹ : L) : Cˣ) : C) := by
  rw [originalSourceGeneratorInverse_det_neg_one,
    originalSourceGeneratorInverse_involute_neg]
  simp

#print axioms originalSourceGeneratorInverse_det_neg_one
#print axioms originalSourceGeneratorInverse_involute_neg
#print axioms originalSourceGeneratorInverse_grade_det_agreement

end
end FCP.BFSSS1V52K1D18J
