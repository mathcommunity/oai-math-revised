import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10RSourceSpinOriginalPaired48SOHomProbe

/-!
K1D18V10H-F10S — the ACTUAL source Clifford negative scalar
has the negative identity gamma16 and exact original paired G1A
48-label matrix image.

The first two interfaces are source-Clifford/algebraic and
matrix-transport facts. The last states the SO48 image of an
ACTUAL source Spin9 term CONDITIONALLY on its Clifford
underlying scalar being negative one.

This stage does NOT construct that source Spin9 negative central
element or assert its membership; those are a distinct next
obligation. No surrogate gamma or changed Fock label order.
No continuous lift, Spin48 lift/cover, Fock action or BFSS
spectral claim.

CANDIDATE until strict pinned warning-as-error Lean and
independent four-declaration type/axiom audits qualify.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Plane
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix
open scoped Kronecker

/-- The original Clifford AlgHom carries REAL scalar -1 to
negative identity in the exact original sixteen-real gamma matrices. -/
theorem source9GammaCliffordAlgHom_neg_one :
    source9GammaCliffordAlgHom
      (-1 : CliffordAlgebra source9Quadratic) =
      -(1 : GammaMatrix) := by
  rw [map_neg, map_one]

/-- The EXACT V10F color-identity Kronecker product and
original G1A paired-Fock permutation preserve matrix negation. -/
theorem gamma16ToOriginalPaired48_neg (A : GammaMatrix) :
    gamma16ToOriginalPaired48 (-A) =
      -(gamma16ToOriginalPaired48 A) := by
  let E := Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv
  have hK :
      ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ (-A)) =
      -((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ A) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.kronecker_apply, Matrix.neg_apply, mul_neg]
  change E ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ (-A)) =
    -(E ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ A))
  rw [hK, map_neg]

/-- The source negative Clifford scalar has precisely the
negative ORIGINAL 48-label identity matrix, not the color-major
surrogate; this does not assert source Spin9 membership. -/
theorem source9OriginalPaired48_neg_scalar_matrix :
    gamma16ToOriginalPaired48
        (source9GammaCliffordAlgHom
          (-1 : CliffordAlgebra source9Quadratic)) =
        -(1 : Matrix Source48Label Source48Label ℝ) := by
  rw [source9GammaCliffordAlgHom_neg_one,
    gamma16ToOriginalPaired48_neg,
    gamma16ToOriginalPaired48_one]

/-- Source-exact CONDITIONAL central-sign action for the
accepted full algebraic Spin9 → original paired SO48 map.
No element with the premise is manufactured by this theorem. -/
theorem source9SpinOriginalPaired48SOHom_neg_scalar_of_mem
    (g : spinGroup source9Quadratic)
    (hg : (g : CliffordAlgebra source9Quadratic) = -1) :
    ((source9SpinOriginalPaired48SpecialOrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ) =
      -(1 : Matrix Source48Label Source48Label ℝ) := by
  rw [source9SpinOriginalPaired48SpecialOrthogonalHom_apply]
  change gamma16ToOriginalPaired48
    ((source9SpinGammaOrthogonalHom g) : GammaMatrix) =
      -(1 : Matrix Source48Label Source48Label ℝ)
  rw [source9SpinGammaOrthogonalHom_apply, hg]
  exact source9OriginalPaired48_neg_scalar_matrix

#print axioms source9GammaCliffordAlgHom_neg_one
#print axioms gamma16ToOriginalPaired48_neg
#print axioms source9OriginalPaired48_neg_scalar_matrix
#print axioms source9SpinOriginalPaired48SOHom_neg_scalar_of_mem

end
end FCP.BFSSPairedSpin9Clifford
