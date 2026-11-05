import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG3B24ModeOrthogonalLiftProbe

/-!
# BFSS SU(2) G3-C — exact complex 24-mode unitary representation

G3-B Gate #96 established an *actual* orthogonal SU(2) action on
the accepted Fin 24 Fock mode labels. Extend its real 24×24
matrices entrywise along ℝ → ℂ. Prove the exact conjugate-transpose
inverse, matrix composition and unitary group homomorphism.

This is a ONE-PARTICLE action. It is not a fermionic gauge action
on the 2^24-dimensional Fock Hilbert space, nor GaugeData.
-/

namespace FCP.BFSSSU2GaugeG3C
noncomputable section

open Matrix
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG3A FCP.BFSSSU2GaugeG3B
open OAI.BFSSQuantum

private abbrev ModeMatrixReal := Matrix (Fin 24) (Fin 24) ℝ
private abbrev ModeMatrixComplex := Matrix (Fin 24) (Fin 24) ℂ

/-- Complex scalar extension of the *actual* G3-B real matrix,
preserving every colorModeEquiv spin-pair index. -/
noncomputable def complexOneParticleMatrix (g : GaugeGroup 2) :
    ModeMatrixComplex :=
  (oneParticleMatrix g).map (algebraMap ℝ ℂ)

/-- Exact block coefficients, no spin-pair mixing. -/
theorem complexOneParticleMatrix_block (g : GaugeGroup 2)
    (j k : Fin 8) (B A : ColorIndex 2) :
    complexOneParticleMatrix g (colorModeEquiv (j,B)) (colorModeEquiv (k,A)) =
      if j = k then (adjointColorMatrix g B A : ℂ) else 0 := by
  by_cases h : j = k
  · simp [complexOneParticleMatrix, Matrix.map_apply, oneParticleMatrix_block, h]
  · simp [complexOneParticleMatrix, Matrix.map_apply, oneParticleMatrix_block, h]

/-- The scalar extension respects the identity SU(2) element. -/
theorem complexOneParticleMatrix_one :
    complexOneParticleMatrix (1 : GaugeGroup 2) = 1 := by
  change (oneParticleMatrix (1 : GaugeGroup 2)).map
    (algebraMap ℝ ℂ) = 1
  rw [oneParticleMatrix_one]
  simp

/-- Exact multiplication; the source-bound coefficient direction is
the SAME as G3-A and G3-B (rows output / columns input). -/
theorem complexOneParticleMatrix_mul (g h : GaugeGroup 2) :
    complexOneParticleMatrix (g * h) =
      complexOneParticleMatrix g * complexOneParticleMatrix h := by
  change (oneParticleMatrix (g*h)).map (algebraMap ℝ ℂ) =
    (oneParticleMatrix g).map (algebraMap ℝ ℂ) *
      (oneParticleMatrix h).map (algebraMap ℝ ℂ)
  rw [oneParticleMatrix_mul, Matrix.map_mul]

/-- Because all real entries have trivial complex conjugation, the
complex conjugate transpose is the scalar-extended real transpose. -/
theorem complexOneParticleMatrix_conjTranspose (g : GaugeGroup 2) :
    (complexOneParticleMatrix g)ᴴ =
      ((oneParticleMatrix g)ᵀ).map (algebraMap ℝ ℂ) := by
  ext i j
  simp [complexOneParticleMatrix, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, Matrix.map_apply]

/-- The true 24-mode complex matrix is isometric: Uᴴ U = I. -/
theorem complexOneParticleMatrix_left_unitary (g : GaugeGroup 2) :
    (complexOneParticleMatrix g)ᴴ * complexOneParticleMatrix g = 1 := by
  rw [complexOneParticleMatrix_conjTranspose]
  change ((oneParticleMatrix g)ᵀ).map (algebraMap ℝ ℂ) *
    (oneParticleMatrix g).map (algebraMap ℝ ℂ) = 1
  rw [← Matrix.map_mul, oneParticleMatrix_orthogonal]
  simp

private theorem complexOneParticleMatrix_inv_right (g : GaugeGroup 2) :
    complexOneParticleMatrix g * complexOneParticleMatrix g⁻¹ = 1 := by
  rw [← complexOneParticleMatrix_mul, mul_inv_cancel,
    complexOneParticleMatrix_one]

private theorem complexOneParticleMatrix_inv_left (g : GaugeGroup 2) :
    complexOneParticleMatrix g⁻¹ * complexOneParticleMatrix g = 1 := by
  rw [← complexOneParticleMatrix_mul, inv_mul_cancel,
    complexOneParticleMatrix_one]

/-- The adjoint is precisely the gauge inverse (not just a left inverse). -/
theorem complexOneParticleMatrix_adjoint_inv (g : GaugeGroup 2) :
    (complexOneParticleMatrix g)ᴴ = complexOneParticleMatrix g⁻¹ := by
  calc
    (complexOneParticleMatrix g)ᴴ =
        (complexOneParticleMatrix g)ᴴ *
          (complexOneParticleMatrix g * complexOneParticleMatrix g⁻¹) := by
            rw [complexOneParticleMatrix_inv_right, mul_one]
    _ = ((complexOneParticleMatrix g)ᴴ * complexOneParticleMatrix g) *
        complexOneParticleMatrix g⁻¹ := by
          simp only [mul_assoc]
    _ = complexOneParticleMatrix g⁻¹ := by
          rw [complexOneParticleMatrix_left_unitary, one_mul]

/-- Right unitarity is verified independently from group inversion. -/
theorem complexOneParticleMatrix_right_unitary (g : GaugeGroup 2) :
    complexOneParticleMatrix g * (complexOneParticleMatrix g)ᴴ = 1 := by
  rw [complexOneParticleMatrix_adjoint_inv]
  exact complexOneParticleMatrix_inv_right g

/-- A genuine element of the pinned matrix unitary group on 24 modes. -/
noncomputable def complexOneParticleUnitary (g : GaugeGroup 2) :
    Matrix.unitaryGroup (Fin 24) ℂ :=
  ⟨complexOneParticleMatrix g, by
    change complexOneParticleMatrix g ∈
      unitary (Matrix (Fin 24) (Fin 24) ℂ)
    rw [Unitary.mem_iff]
    exact ⟨complexOneParticleMatrix_left_unitary g,
      complexOneParticleMatrix_right_unitary g⟩⟩

/-- Exact SU(2) group homomorphism into the real-origin complex
24-mode unitary matrices. The Fock representation still needs a
separate ExteriorAlgebra.map / unitary-conjugation construction. -/
noncomputable def complexOneParticleUnitaryHom :
    GaugeGroup 2 →* Matrix.unitaryGroup (Fin 24) ℂ where
  toFun := complexOneParticleUnitary
  map_one' := by
    apply Subtype.ext
    change complexOneParticleMatrix 1 = 1
    exact complexOneParticleMatrix_one
  map_mul' g h := by
    apply Subtype.ext
    change complexOneParticleMatrix (g*h) =
      complexOneParticleMatrix g * complexOneParticleMatrix h
    exact complexOneParticleMatrix_mul g h

#print axioms complexOneParticleMatrix_block
#print axioms complexOneParticleMatrix_one
#print axioms complexOneParticleMatrix_mul
#print axioms complexOneParticleMatrix_conjTranspose
#print axioms complexOneParticleMatrix_left_unitary
#print axioms complexOneParticleMatrix_adjoint_inv
#print axioms complexOneParticleMatrix_right_unitary
#print axioms complexOneParticleUnitary
#print axioms complexOneParticleUnitaryHom

end
end FCP.BFSSSU2GaugeG3C
