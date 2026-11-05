import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9SourceSpinGammaMatrixUnitsProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
K1D18V10E — source-exact global algebraic Spin9 gamma
matrix orthogonality, via Clifford grade reversal and
the pinned even Spin-group star identity.

This is an experimental proof chain, NOT QUALIFIED until
the strict warningAsError and independent axiom gate succeeds.

The gamma family is the unchanged accepted real 16x16
FCP.BFSSGamma9.gamma. The source group is the ACTUAL
spinGroup source9Quadratic. No replacement matrix, Clifford
model, group, central-sign assertion or arbitrary continuity
instance is introduced. The target here is O(16), NOT the
original paired Fock SO(48).
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSGamma9
open Matrix

/-- The exact accepted real nine-gamma matrix linear combination
is symmetric for every source nine-vector, not just each basis
gamma. -/
theorem gammaNineRealLinear_transpose (v : SpaceIndex → ℝ) :
    (gammaNineRealLinear v).transpose = gammaNineRealLinear v := by
  change (∑ i : SpaceIndex, (v i) • gamma i).transpose =
    ∑ i : SpaceIndex, (v i) • gamma i
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.transpose_smul, gamma_symmetric i]

/-- The original universal Clifford gamma representation
intertwines *grade reversal* with real matrix transpose.
This does not claim that Clifford star is transpose on odd
elements (it is not, by the pinned source). -/
theorem source9GammaCliffordAlgHom_reverse
    (a : CliffordAlgebra source9Quadratic) :
    source9GammaCliffordAlgHom (CliffordAlgebra.reverse a) =
      (source9GammaCliffordAlgHom a).transpose := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
      have hreverse :
          CliffordAlgebra.reverse
            (algebraMap ℝ (CliffordAlgebra source9Quadratic) r) =
          algebraMap ℝ (CliffordAlgebra source9Quadratic) r :=
        CliffordAlgebra.reverse.commutes r
      have hgamma :
          source9GammaCliffordAlgHom
            (algebraMap ℝ (CliffordAlgebra source9Quadratic) r) =
          algebraMap ℝ GammaMatrix r :=
        source9GammaCliffordAlgHom.commutes r
      calc
        source9GammaCliffordAlgHom
            (CliffordAlgebra.reverse
              (algebraMap ℝ (CliffordAlgebra source9Quadratic) r)) =
          source9GammaCliffordAlgHom
            (algebraMap ℝ (CliffordAlgebra source9Quadratic) r) :=
          congrArg source9GammaCliffordAlgHom hreverse
        _ = algebraMap ℝ GammaMatrix r := hgamma
        _ = (algebraMap ℝ GammaMatrix r).transpose := by
          rw [Algebra.algebraMap_eq_smul_one,
            Matrix.transpose_smul, Matrix.transpose_one]
        _ = (source9GammaCliffordAlgHom
            (algebraMap ℝ (CliffordAlgebra source9Quadratic) r)).transpose :=
          congrArg Matrix.transpose hgamma.symm
  | ι v =>
      simpa only [CliffordAlgebra.reverse_ι,
        source9GammaCliffordAlgHom_generator] using
        (gammaNineRealLinear_transpose v).symm
  | mul a b ha hb =>
      simp only [CliffordAlgebra.reverse.map_mul, map_mul,
        Matrix.transpose_mul, ha, hb]
  | add a b ha hb =>
      simp only [map_add, Matrix.transpose_add, ha, hb]

/-- On the ACTUAL even source Spin9 subgroup, the Clifford
star involution specializes to grade reversal; its image
is therefore the transpose of the original gamma matrix. -/
theorem source9SpinGammaMatrix_star_transpose
    (g : spinGroup source9Quadratic) :
    source9GammaCliffordAlgHom
      (star (g : CliffordAlgebra source9Quadratic)) =
        (source9GammaCliffordAlgHom
          (g : CliffordAlgebra source9Quadratic)).transpose := by
  rw [CliffordAlgebra.star_def, spinGroup.involute_eq g.property]
  exact source9GammaCliffordAlgHom_reverse
    (g : CliffordAlgebra source9Quadratic)

/-- The exact V10D full Spin9 source group representation
has orthogonal real matrix image, not merely invertible image.
The inverse-transpose identity follows from the actual
Spin-group Clifford unitary condition, not a guessed sign. -/
theorem source9SpinGammaMatrix_mem_orthogonalGroup
    (g : spinGroup source9Quadratic) :
    ((source9SpinGammaMatrixUnitsHom g) : GammaMatrix) ∈
      Matrix.orthogonalGroup SpinIndex ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  rw [source9SpinGammaMatrixUnitsHom_apply]
  calc
    source9GammaCliffordAlgHom
        (g : CliffordAlgebra source9Quadratic) *
      (source9GammaCliffordAlgHom
        (g : CliffordAlgebra source9Quadratic)).transpose =
      source9GammaCliffordAlgHom
        (g : CliffordAlgebra source9Quadratic) *
        source9GammaCliffordAlgHom
          (star (g : CliffordAlgebra source9Quadratic)) := by
            rw [source9SpinGammaMatrix_star_transpose g]
    _ = source9GammaCliffordAlgHom
          ((g : CliffordAlgebra source9Quadratic) *
            star (g : CliffordAlgebra source9Quadratic)) := by
          rw [map_mul]
    _ = 1 := by
      rw [spinGroup.mul_star_self_of_mem g.property, map_one]

/-- A global algebraic source Spin(9) group homomorphism
into the GENUINE pinned 16-real-dimensional orthogonal group.
Unlike the previously accepted V10B one-parameter maps,
the domain is all of spinGroup source9Quadratic. -/
noncomputable def source9SpinGammaOrthogonalHom :
    spinGroup source9Quadratic →*
      Matrix.orthogonalGroup SpinIndex ℝ where
  toFun g :=
    ⟨((source9SpinGammaMatrixUnitsHom g) : GammaMatrix),
      source9SpinGammaMatrix_mem_orthogonalGroup g⟩
  map_one' := by
    apply Subtype.ext
    change ((source9SpinGammaMatrixUnitsHom
      (1 : spinGroup source9Quadratic)) : GammaMatrix) = 1
    rw [map_one]
    rfl
  map_mul' := by
    intro g h
    apply Subtype.ext
    change ((source9SpinGammaMatrixUnitsHom (g * h)) :
        GammaMatrix) =
      ((source9SpinGammaMatrixUnitsHom g : GammaMatrixˣ) :
        GammaMatrix) *
      ((source9SpinGammaMatrixUnitsHom h : GammaMatrixˣ) :
        GammaMatrix)
    rw [map_mul]
    rfl

/-- The true global orthogonal group homomorphism has exactly
the original source nine-gamma Clifford-algebra evaluation. -/
theorem source9SpinGammaOrthogonalHom_apply
    (g : spinGroup source9Quadratic) :
    ((source9SpinGammaOrthogonalHom g) : GammaMatrix) =
      source9GammaCliffordAlgHom
        (g : CliffordAlgebra source9Quadratic) := by
  exact source9SpinGammaMatrixUnitsHom_apply g

#print axioms gammaNineRealLinear_transpose
#print axioms source9GammaCliffordAlgHom_reverse
#print axioms source9SpinGammaMatrix_star_transpose
#print axioms source9SpinGammaMatrix_mem_orthogonalGroup
#print axioms source9SpinGammaOrthogonalHom
#print axioms source9SpinGammaOrthogonalHom_apply

end
end FCP.BFSSPairedSpin9Clifford
