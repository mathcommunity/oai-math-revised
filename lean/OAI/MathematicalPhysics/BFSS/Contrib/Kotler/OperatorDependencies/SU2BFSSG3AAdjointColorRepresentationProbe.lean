import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG2BBosonGaugeContinuityProbe
import OAI.MathematicalPhysics.BFSS.CovariantFields

/-!
# BFSS SU(2) G3-A — actual adjoint color coefficient matrix

For the accepted paired AlgebraData 2, define the exact 3×3 real
color matrix R(g) with rows = output colors B, columns = input A:
  R(g) B A = M.adjointCoefficient g A B.

Prove its identity, composition, and real orthonormality using the
pinned colorConjugate_coefficient, colorConjugate_mul and
colorConjugate_inner lemmas. No fermionic gauge representation
or physical/spectral theorem is asserted.
-/

namespace FCP.BFSSSU2GaugeG3A
noncomputable section

open Matrix Finset
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A

private abbrev M : AlgebraData 2 := pairedAlgebraData

/-- The actual standard basis of three real SU(2) color coordinates. -/
noncomputable def colorUnit (A : ColorIndex 2) : ColorVector 2 :=
  WithLp.toLp 2 (fun B => if B = A then 1 else 0)

@[simp] theorem colorUnit_apply (A B : ColorIndex 2) :
    colorUnit A B = if B = A then 1 else 0 := rfl

/-- The real input-color unit basis is exactly orthonormal. -/
theorem colorUnit_inner (A D : ColorIndex 2) :
    inner ℝ (colorUnit A) (colorUnit D) =
      if A = D then 1 else 0 := by
  simp [colorUnit, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  by_cases h : A = D
  · subst D
    simp
  · simp [h, Ne.symm h]

/-- The actual pinned adjointCoefficient g A B is the B-th coordinate
of the conjugated A-th unit basis vector, fixing index direction. -/
theorem adjointCoefficient_on_basis (g : GaugeGroup 2)
    (A B : ColorIndex 2) :
    (M.colorConjugate (g : ColorMatrix 2) (colorUnit A)) B =
      M.adjointCoefficient g A B := by
  rw [M.colorConjugate_coefficient g (colorUnit A) B]
  simp [colorUnit, mul_ite]

/-- The coefficient's group identity has A=input, B=output. -/
theorem adjointCoefficient_one (A B : ColorIndex 2) :
    M.adjointCoefficient (1 : GaugeGroup 2) A B =
      if A = B then 1 else 0 := by
  calc
    _ = (M.colorConjugate (1 : ColorMatrix 2) (colorUnit A)) B :=
      (adjointCoefficient_on_basis 1 A B).symm
    _ = (colorUnit A) B :=
      congrArg (fun v : ColorVector 2 => v B)
        (M.colorConjugate_one (colorUnit A))
    _ = if A = B then 1 else 0 := by
      simp [colorUnit, eq_comm]

/-- Exact composition: M.adjointCoefficient g A B transforms INPUT
color A to OUTPUT color B. -/
theorem adjointCoefficient_mul
    (g h : GaugeGroup 2) (A C : ColorIndex 2) :
    M.adjointCoefficient (g * h) A C =
      ∑ B : ColorIndex 2,
        M.adjointCoefficient g B C * M.adjointCoefficient h A B := by
  calc
    _ = (M.colorConjugate ((g * h : GaugeGroup 2) : ColorMatrix 2)
      (colorUnit A)) C := (adjointCoefficient_on_basis (g * h) A C).symm
    _ = (M.colorConjugate (g : ColorMatrix 2)
      (M.colorConjugate (h : ColorMatrix 2) (colorUnit A))) C := by
        exact congrArg (fun v : ColorVector 2 => v C)
          (M.colorConjugate_mul (g : ColorMatrix 2)
            (h : ColorMatrix 2) h.prop.1 (colorUnit A))
    _ = ∑ B : ColorIndex 2,
        M.adjointCoefficient g B C *
          (M.colorConjugate (h : ColorMatrix 2) (colorUnit A)) B :=
      M.colorConjugate_coefficient g _ C
    _ = ∑ B : ColorIndex 2,
        M.adjointCoefficient g B C * M.adjointCoefficient h A B := by
      apply Finset.sum_congr rfl
      intro B _
      rw [adjointCoefficient_on_basis h A B]

/-- Exact orthonormality of input color columns of the real adjoint
matrix; follows from the *pinned* inner-product isometry. -/
theorem adjointCoefficient_orthogonal (g : GaugeGroup 2)
    (A D : ColorIndex 2) :
    (∑ B : ColorIndex 2,
      M.adjointCoefficient g A B * M.adjointCoefficient g D B) =
        if A = D then 1 else 0 := by
  calc
    _ = ∑ B : ColorIndex 2,
        (M.colorConjugate (g : ColorMatrix 2) (colorUnit A)) B *
          (M.colorConjugate (g : ColorMatrix 2) (colorUnit D)) B := by
      apply Finset.sum_congr rfl
      intro B _
      rw [adjointCoefficient_on_basis g A B,
        adjointCoefficient_on_basis g D B]
    _ = inner ℝ (M.colorConjugate (g : ColorMatrix 2) (colorUnit A))
          (M.colorConjugate (g : ColorMatrix 2) (colorUnit D)) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ = inner ℝ (colorUnit A) (colorUnit D) :=
      M.colorConjugate_inner (g : ColorMatrix 2) g.prop.1 _ _
    _ = if A = D then 1 else 0 := colorUnit_inner A D

/-- Correct rows=output, columns=input orientation; this is the
real 3×3 matrix to rotate colors in each of the eight Fock mode pairs. -/
noncomputable def adjointColorMatrix (g : GaugeGroup 2) :
    Matrix (ColorIndex 2) (ColorIndex 2) ℝ :=
  fun B A => M.adjointCoefficient g A B

theorem adjointColorMatrix_one :
    adjointColorMatrix (1 : GaugeGroup 2) = 1 := by
  ext B A
  change M.adjointCoefficient 1 A B = if B = A then (1 : ℝ) else 0
  rw [adjointCoefficient_one]
  by_cases h : A = B
  · subst B
    simp
  · simp [h, Ne.symm h]

theorem adjointColorMatrix_mul (g h : GaugeGroup 2) :
    adjointColorMatrix (g * h) =
      adjointColorMatrix g * adjointColorMatrix h := by
  ext C A
  simpa only [adjointColorMatrix, Matrix.mul_apply] using
    adjointCoefficient_mul g h A C

theorem adjointColorMatrix_orthogonal (g : GaugeGroup 2) :
    (adjointColorMatrix g)ᵀ * adjointColorMatrix g = 1 := by
  ext A D
  simpa only [Matrix.mul_apply, Matrix.transpose_apply,
    adjointColorMatrix, Matrix.one_apply] using
    adjointCoefficient_orthogonal g A D

#print axioms colorUnit_inner
#print axioms adjointCoefficient_on_basis
#print axioms adjointCoefficient_one
#print axioms adjointCoefficient_mul
#print axioms adjointCoefficient_orthogonal
#print axioms adjointColorMatrix_one
#print axioms adjointColorMatrix_mul
#print axioms adjointColorMatrix_orthogonal

end
end FCP.BFSSSU2GaugeG3A
