import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1COneParticleSpecialUnitaryProbe

/-!
S1J: the ACTUAL 48-real-dimensional original SU(2) Majorana color
representation, on the existing accepted 24-complex-mode Fock labeling.

For each original complex Fock mode there are exactly two real Majoranas.
The actual source color rotation acts identically on both real components.
This matrix is the Kronecker product R24(g) ⊗ I2 on the exact
(Fin 24 × Fin 2) original paired Majorana labels, with the original
+ i SU(2) adjoint color coefficient orientation preserved.

No external paper Spin(48) lift is constructed; this proof checks the
precise source REAL orthogonal SO(48) input data for attempting that lift.
-/

set_option autoImplicit false
set_option maxHeartbeats 220000

namespace FCP.BFSSSU2PhysicalDomainS1J
noncomputable section

open scoped Kronecker
open Matrix
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG3B
open FCP.BFSSSU2PhysicalDomainS1C
open OAI.BFSSQuantum

/-- 48 real Majorana labels, precisely the accepted pairedLabelEquiv
codomain; the real/imaginary Majoranas of each original mode stay separate. -/
abbrev OriginalMajoranaLabel := Fin 24 × Fin 2
abbrev OriginalMajoranaMatrix :=
  Matrix OriginalMajoranaLabel OriginalMajoranaLabel ℝ

/-- Exact direct action on BOTH real Majoranas per original 24-mode Fock
label: no independently chosen 48×48 orthogonal matrix. -/
noncomputable def sourceRealMajoranaMatrix (g : GaugeGroup 2) :
    OriginalMajoranaMatrix :=
  Matrix.kronecker (oneParticleMatrix g) (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- Every 48×48 entry is the original real Fock color matrix coefficient,
diagonal in the two real Majorana components of a complex mode. -/
theorem sourceRealMajoranaMatrix_entry (g : GaugeGroup 2)
    (m n : Fin 24) (s t : Fin 2) :
    sourceRealMajoranaMatrix g (m,s) (n,t) =
      if s = t then oneParticleMatrix g m n else 0 := by
  simp [sourceRealMajoranaMatrix, Matrix.kronecker, Matrix.one_apply,
    mul_ite, mul_one, mul_zero]

theorem sourceRealMajoranaMatrix_one :
    sourceRealMajoranaMatrix (1 : GaugeGroup 2) = 1 := by
  change Matrix.kronecker (oneParticleMatrix 1)
    (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1
  rw [oneParticleMatrix_one]
  exact Matrix.one_kronecker_one

theorem sourceRealMajoranaMatrix_mul (g h : GaugeGroup 2) :
    sourceRealMajoranaMatrix (g*h) =
      sourceRealMajoranaMatrix g * sourceRealMajoranaMatrix h := by
  calc
    sourceRealMajoranaMatrix (g*h) =
      Matrix.kronecker (oneParticleMatrix g * oneParticleMatrix h)
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
          rw [sourceRealMajoranaMatrix, oneParticleMatrix_mul]
    _ = Matrix.kronecker (oneParticleMatrix g * oneParticleMatrix h)
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) * 1) := by
          rw [mul_one]
    _ = sourceRealMajoranaMatrix g * sourceRealMajoranaMatrix h :=
      Matrix.mul_kronecker_mul _ _ _ _

theorem sourceRealMajoranaMatrix_transpose (g : GaugeGroup 2) :
    (sourceRealMajoranaMatrix g)ᵀ =
      Matrix.kronecker (oneParticleMatrix g)ᵀ
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext ⟨m,s⟩ ⟨n,t⟩
  simp [sourceRealMajoranaMatrix, Matrix.kronecker,
    Matrix.one_apply, Matrix.transpose_apply, eq_comm]

/-- The actual source 48-dimensional color action is orthogonal. -/
theorem sourceRealMajoranaMatrix_orthogonal (g : GaugeGroup 2) :
    (sourceRealMajoranaMatrix g)ᵀ * sourceRealMajoranaMatrix g = 1 := by
  calc
    _ = Matrix.kronecker (oneParticleMatrix g)ᵀ
          (1 : Matrix (Fin 2) (Fin 2) ℝ) *
        Matrix.kronecker (oneParticleMatrix g)
          (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
            rw [sourceRealMajoranaMatrix_transpose, sourceRealMajoranaMatrix]
    _ = Matrix.kronecker
        ((oneParticleMatrix g)ᵀ * oneParticleMatrix g)
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) * 1) :=
      (Matrix.mul_kronecker_mul _ _ _ _).symm
    _ = 1 := by
      rw [oneParticleMatrix_orthogonal, mul_one]
      exact Matrix.one_kronecker_one

/-- The determinant is exactly +1, not merely ±1: the accepted real
24-mode color rotation is duplicated on both real Majoranas. -/
theorem sourceRealMajoranaMatrix_det_one (g : GaugeGroup 2) :
    (sourceRealMajoranaMatrix g).det = 1 := by
  change ((oneParticleMatrix g) ⊗ₖ
    (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 1
  rw [Matrix.det_kronecker]
  simp [oneParticleMatrix_det_one]

/-- The SO(48)-matrix-valued SU(2) action has an exact homomorphism,
with no assumed continuity or double-cover lift. -/
noncomputable def sourceRealMajoranaMatrixHom :
    GaugeGroup 2 →* OriginalMajoranaMatrix where
  toFun := sourceRealMajoranaMatrix
  map_one' := sourceRealMajoranaMatrix_one
  map_mul' := sourceRealMajoranaMatrix_mul

#print axioms sourceRealMajoranaMatrix
#print axioms sourceRealMajoranaMatrix_entry
#print axioms sourceRealMajoranaMatrix_one
#print axioms sourceRealMajoranaMatrix_mul
#print axioms sourceRealMajoranaMatrix_transpose
#print axioms sourceRealMajoranaMatrix_orthogonal
#print axioms sourceRealMajoranaMatrix_det_one
#print axioms sourceRealMajoranaMatrixHom

end
end FCP.BFSSSU2PhysicalDomainS1J
