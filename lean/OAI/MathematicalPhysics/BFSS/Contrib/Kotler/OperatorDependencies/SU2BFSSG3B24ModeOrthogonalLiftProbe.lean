import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG3AAdjointColorRepresentationProbe

/-!
# BFSS SU(2) G3-B — exact 24-mode real orthogonal color representation

The qualified G3-A SU(2) adjointColorMatrix rotates three colors.
Use an identity eight-pair factor and the *accepted* colorModeEquiv
to lift it into the literal Fin 24 Fock creation/annihilation indices.

The resulting 24×24 real matrix has verified block, identity,
multiplication and orthogonality properties if this gate compiles.
No Fock-space implementer or fermionic GaugeData field is constructed.
-/

namespace FCP.BFSSSU2GaugeG3B
noncomputable section

open Matrix
open FCP.BFSSSU2GaugeG1A FCP.BFSSSU2GaugeG3A
open OAI.BFSSQuantum

private abbrev ColorModes := Fin 8 × ColorIndex 2
private abbrev ModeMatrix := Matrix ColorModes ColorModes ℝ

/-- Eight independent spin-pair blocks, each carrying the actual
source-bound three-color adjoint SU(2) rotation. -/
noncomputable def colorBlocks (g : GaugeGroup 2) : ModeMatrix :=
  Matrix.kronecker (1 : Matrix (Fin 8) (Fin 8) ℝ) (adjointColorMatrix g)

/-- Index transport uses the already accepted 8×3 ≃ 24 Fock labeling.
It is a real matrix algebra equivalence, hence preserves products. -/
noncomputable def modeReindex :
    ModeMatrix ≃ₐ[ℝ] Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ colorModeEquiv

/-- Real SU(2) action on all twenty-four indexed Fock modes. -/
noncomputable def oneParticleMatrix (g : GaugeGroup 2) :
    Matrix (Fin 24) (Fin 24) ℝ :=
  modeReindex (colorBlocks g)

/-- Fixed spin pair j carries R(g); distinct j blocks never mix. -/
theorem oneParticleMatrix_block (g : GaugeGroup 2)
    (j k : Fin 8) (B A : ColorIndex 2) :
    oneParticleMatrix g (colorModeEquiv (j,B)) (colorModeEquiv (k,A)) =
      if j = k then adjointColorMatrix g B A else 0 := by
  simp [oneParticleMatrix, modeReindex, colorBlocks,
    Matrix.reindex, Matrix.kronecker, Matrix.one_apply]

private theorem colorBlocks_one :
    colorBlocks (1 : GaugeGroup 2) = 1 := by
  rw [colorBlocks, adjointColorMatrix_one]
  exact Matrix.one_kronecker_one

private theorem colorBlocks_mul (g h : GaugeGroup 2) :
    colorBlocks (g * h) = colorBlocks g * colorBlocks h := by
  calc
    colorBlocks (g * h) =
        Matrix.kronecker (1 : Matrix (Fin 8) (Fin 8) ℝ)
          (adjointColorMatrix g * adjointColorMatrix h) := by
            rw [colorBlocks, adjointColorMatrix_mul]
    _ = Matrix.kronecker
          ((1 : Matrix (Fin 8) (Fin 8) ℝ) * 1)
          (adjointColorMatrix g * adjointColorMatrix h) := by
            rw [Matrix.one_mul]
    _ = colorBlocks g * colorBlocks h := by
      exact Matrix.mul_kronecker_mul _ _ _ _

/-- The 24-mode matrix is the exact group identity at g=1. -/
theorem oneParticleMatrix_one :
    oneParticleMatrix (1 : GaugeGroup 2) = 1 := by
  change modeReindex (colorBlocks 1) = 1
  rw [colorBlocks_one]
  exact map_one modeReindex

/-- Correct SU(2) group law, without reversing input/output colors. -/
theorem oneParticleMatrix_mul (g h : GaugeGroup 2) :
    oneParticleMatrix (g * h) =
      oneParticleMatrix g * oneParticleMatrix h := by
  change modeReindex (colorBlocks (g * h)) =
    modeReindex (colorBlocks g) * modeReindex (colorBlocks h)
  rw [colorBlocks_mul]
  exact map_mul modeReindex (colorBlocks g) (colorBlocks h)

/-- The block tensor transpose is componentwise transpose. -/
private theorem colorBlocks_transpose (g : GaugeGroup 2) :
    (colorBlocks g)ᵀ =
      Matrix.kronecker (1 : Matrix (Fin 8) (Fin 8) ℝ)
        (adjointColorMatrix g)ᵀ := by
  ext ⟨j,B⟩ ⟨k,A⟩
  simp [colorBlocks, Matrix.kronecker, Matrix.one_apply,
    Matrix.transpose_apply, eq_comm]

/-- Each 3-color block is orthogonal, hence all 24 modes are. -/
private theorem colorBlocks_orthogonal (g : GaugeGroup 2) :
    (colorBlocks g)ᵀ * colorBlocks g = 1 := by
  calc
    _ = Matrix.kronecker (1 : Matrix (Fin 8) (Fin 8) ℝ)
          (adjointColorMatrix g)ᵀ *
        Matrix.kronecker (1 : Matrix (Fin 8) (Fin 8) ℝ)
          (adjointColorMatrix g) := by
            rw [colorBlocks_transpose, colorBlocks]
    _ = Matrix.kronecker
          ((1 : Matrix (Fin 8) (Fin 8) ℝ) * 1)
          ((adjointColorMatrix g)ᵀ * adjointColorMatrix g) := by
            exact (Matrix.mul_kronecker_mul _ _ _ _).symm
    _ = 1 := by
      rw [Matrix.one_mul, adjointColorMatrix_orthogonal]
      exact Matrix.one_kronecker_one

/-- Algebraic index reindexing commutes with matrix transposition. -/
private theorem modeReindex_transpose (X : ModeMatrix) :
    (modeReindex X)ᵀ = modeReindex Xᵀ := by
  ext i j
  rfl

/-- Real orthogonality on the literal 24 Fock mode index. -/
theorem oneParticleMatrix_orthogonal (g : GaugeGroup 2) :
    (oneParticleMatrix g)ᵀ * oneParticleMatrix g = 1 := by
  change (modeReindex (colorBlocks g))ᵀ *
    modeReindex (colorBlocks g) = 1
  calc
    _ = modeReindex (colorBlocks g)ᵀ * modeReindex (colorBlocks g) := by
      rw [modeReindex_transpose]
    _ = modeReindex ((colorBlocks g)ᵀ * colorBlocks g) :=
      (map_mul modeReindex _ _).symm
    _ = 1 := by
      rw [colorBlocks_orthogonal]
      exact map_one modeReindex

#print axioms oneParticleMatrix_block
#print axioms oneParticleMatrix_one
#print axioms oneParticleMatrix_mul
#print axioms oneParticleMatrix_orthogonal

end
end FCP.BFSSSU2GaugeG3B
