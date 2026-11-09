import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9SourceSpinGammaOrthogonalProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9PlaneGeneratorProbe

/-!
K1D18V10F — source-exact transfer of the globally qualified
algebraic Spin(9) orthogonal gamma action from 16 real spinor
indices to the original 48 real *paired Fock* indices.

This is the ACTUAL accepted G1A pairedColorSpinEquiv, NOT a
color-major replacement. The transfer is Kronecker by the
identity on the original three color labels, followed by the
exact earlier proved Matrix.reindexRingEquiv. Both the
multiplicative and transpose interfaces are proved explicitly.

The proposed result is an algebraic group homomorphism into
O(original 48). It is NOT yet SO(original 48), a continuous
Spin(9) Lie-group homomorphism, the original Spin48 lift,
a Fock-unitary theorem, or a BFSS physical/spectral claim.

CANDIDATE UNTIL STRICT COMPILER AND INDEPENDENT AXIOM GATE.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSPairedSpin9Plane
open Matrix
open scoped Kronecker

/-- Exact original paired-Fock index transport of one 16-real
spinor matrix, with identity on the three source colors. -/
noncomputable def gamma16ToOriginalPaired48
    (A : GammaMatrix) : Matrix Source48Label Source48Label ℝ :=
  (Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv)
    ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ A)

/-- The actual original paired-index transport preserves one. -/
theorem gamma16ToOriginalPaired48_one :
    gamma16ToOriginalPaired48 (1 : GammaMatrix) =
      (1 : Matrix Source48Label Source48Label ℝ) := by
  unfold gamma16ToOriginalPaired48
  rw [Matrix.one_kronecker_one, map_one]

/-- Multiplication is preserved by Kronecker color identity
and by the exact original index reindexing ring equivalence. -/
theorem gamma16ToOriginalPaired48_mul (A B : GammaMatrix) :
    gamma16ToOriginalPaired48 (A * B) =
      gamma16ToOriginalPaired48 A *
        gamma16ToOriginalPaired48 B := by
  let E := Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv
  change E ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ (A * B)) =
    E ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ A) *
    E ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ B)
  rw [← map_mul]
  apply congrArg E
  simpa only [one_mul] using
    (Matrix.mul_kronecker_mul
      (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ)
      (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) A B)

/-- Original paired-index transport commutes with real matrix
transpose. Reindexing respects the *original* Fock label order. -/
theorem gamma16ToOriginalPaired48_transpose (A : GammaMatrix) :
    (gamma16ToOriginalPaired48 A).transpose =
      gamma16ToOriginalPaired48 A.transpose := by
  let E := Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv
  let B : Matrix (ColorIndex 2 × SpinIndex)
      (ColorIndex 2 × SpinIndex) ℝ :=
    (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ A
  have htransport (M : Matrix (ColorIndex 2 × SpinIndex)
      (ColorIndex 2 × SpinIndex) ℝ) :
      (E M).transpose = E M.transpose := by
    ext p q
    rfl
  change (E B).transpose =
    E ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ A.transpose)
  calc
    (E B).transpose = E B.transpose := htransport B
    _ = E ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ).transpose
      ⊗ₖ A.transpose) := by
        exact congrArg E
          (Matrix.kroneckerMap_transpose (· * ·)
            (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) A).symm
    _ = E ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ)
      ⊗ₖ A.transpose) := by rw [Matrix.transpose_one]

/-- Actual gamma transport carries orthogonal 16-real
matrices into orthogonal matrices on the original paired-48
source indices. Invertibility alone is not substituted. -/
theorem gamma16ToOriginalPaired48_mem_orthogonalGroup
    (A : GammaMatrix)
    (hA : A ∈ Matrix.orthogonalGroup SpinIndex ℝ) :
    gamma16ToOriginalPaired48 A ∈
      Matrix.orthogonalGroup Source48Label ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff] at hA ⊢
  calc
    gamma16ToOriginalPaired48 A *
        (gamma16ToOriginalPaired48 A).transpose =
      gamma16ToOriginalPaired48 A *
        gamma16ToOriginalPaired48 A.transpose := by
          rw [gamma16ToOriginalPaired48_transpose]
    _ = gamma16ToOriginalPaired48 (A * A.transpose) :=
      (gamma16ToOriginalPaired48_mul A A.transpose).symm
    _ = gamma16ToOriginalPaired48 (1 : GammaMatrix) := by
      rw [hA]
    _ = 1 := gamma16ToOriginalPaired48_one

/-- Global *algebraic* homomorphism from the actual source
Spin9 group into O(48) on the ACTUAL original G1A paired
Fock labels. No source Spin9 topology is assumed. -/
noncomputable def source9SpinOriginalPaired48OrthogonalHom :
    spinGroup source9Quadratic →*
      Matrix.orthogonalGroup Source48Label ℝ where
  toFun g :=
    ⟨gamma16ToOriginalPaired48
      ((source9SpinGammaOrthogonalHom g) : GammaMatrix),
      gamma16ToOriginalPaired48_mem_orthogonalGroup
        ((source9SpinGammaOrthogonalHom g) : GammaMatrix)
        (source9SpinGammaOrthogonalHom g).property⟩
  map_one' := by
    apply Subtype.ext
    change gamma16ToOriginalPaired48
      ((source9SpinGammaOrthogonalHom
        (1 : spinGroup source9Quadratic)) : GammaMatrix) = 1
    have h :
        ((source9SpinGammaOrthogonalHom
          (1 : spinGroup source9Quadratic)) : GammaMatrix) = 1 := by
      rw [map_one]
      rfl
    rw [h]
    exact gamma16ToOriginalPaired48_one
  map_mul' := by
    intro g h
    apply Subtype.ext
    change gamma16ToOriginalPaired48
      ((source9SpinGammaOrthogonalHom (g * h)) : GammaMatrix) =
      gamma16ToOriginalPaired48
        ((source9SpinGammaOrthogonalHom g) : GammaMatrix) *
      gamma16ToOriginalPaired48
        ((source9SpinGammaOrthogonalHom h) : GammaMatrix)
    have hm :
        ((source9SpinGammaOrthogonalHom (g * h)) : GammaMatrix) =
        ((source9SpinGammaOrthogonalHom g) : GammaMatrix) *
        ((source9SpinGammaOrthogonalHom h) : GammaMatrix) := by
      rw [map_mul]
      rfl
    rw [hm]
    exact gamma16ToOriginalPaired48_mul
      ((source9SpinGammaOrthogonalHom g) : GammaMatrix)
      ((source9SpinGammaOrthogonalHom h) : GammaMatrix)

/-- Exact new source-group homomorphism evaluation on the
original 48 labels: the actual color-identity Kronecker
factor and the accepted, non-color-major paired permutation. -/
theorem source9SpinOriginalPaired48OrthogonalHom_apply
    (g : spinGroup source9Quadratic) :
    ((source9SpinOriginalPaired48OrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ) =
      (Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv)
        ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ
          ((source9SpinGammaOrthogonalHom g) : GammaMatrix)) := rfl

#print axioms gamma16ToOriginalPaired48_one
#print axioms gamma16ToOriginalPaired48_mul
#print axioms gamma16ToOriginalPaired48_transpose
#print axioms gamma16ToOriginalPaired48_mem_orthogonalGroup
#print axioms source9SpinOriginalPaired48OrthogonalHom
#print axioms source9SpinOriginalPaired48OrthogonalHom_apply

end
end FCP.BFSSPairedSpin9Clifford
