import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10UActualNegativeCentralSO48ImageProbe

/-!
K1D18V10H-F10V — genuine source Spin9 negative central
involution, commutativity, and exact original G1A paired-label
SO48 sign action.

Accepted F10T constructs -1 as an ACTUAL source Spin9 element.
Accepted F10U verifies its original paired SO48 image is -I48
and the element is not in that representation's kernel.

This bounded step now checks that the element squares to the
source Spin9 identity and commutes with EVERY actual source
Spin9 element, then derives the left and right matrix sign
actions by the ACCEPTED original paired SO48 MonoidHom.

No substitution of 48-dimensional Spin48 for source Spin9.
No faithfulness/whole-kernel classification, topology, lift,
Fock implementer, BFSS gauge or spectral physics asserted.

CANDIDATE pending pinned strict warning-as-error compilation
and independent four-declaration exact type/axiom checks.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- The original source Spin9 negative Clifford scalar is an
involution, using only its accepted genuine Spin9 membership. -/
theorem source9NegativeCentral_sq_eq_one :
    source9NegativeCentral * source9NegativeCentral =
      (1 : spinGroup source9Quadratic) := by
  apply Subtype.ext
  change (-1 : CliffordAlgebra source9Quadratic) *
      (-1 : CliffordAlgebra source9Quadratic) = 1
  simp

/-- Source-exact centrality: multiplication by the genuine
negative Clifford scalar commutes with every actual Spin9
element, rather than a surrogate group element. -/
theorem source9NegativeCentral_mul_comm
    (g : spinGroup source9Quadratic) :
    source9NegativeCentral * g = g * source9NegativeCentral := by
  apply Subtype.ext
  change (-1 : CliffordAlgebra source9Quadratic) *
      (g : CliffordAlgebra source9Quadratic) =
      (g : CliffordAlgebra source9Quadratic) *
      (-1 : CliffordAlgebra source9Quadratic)
  simp

/-- The accepted full source Spin9 → SO(original paired48)
homomorphism sends left-multiplication by the actual central
negative scalar to matrix negation on the original labels. -/
theorem source9NegativeCentral_originalPairedSO48_left_sign
    (g : spinGroup source9Quadratic) :
    ((source9SpinOriginalPaired48SpecialOrthogonalHom
        (source9NegativeCentral * g)) :
      Matrix Source48Label Source48Label ℝ) =
    -((source9SpinOriginalPaired48SpecialOrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ) := by
  calc
    ((source9SpinOriginalPaired48SpecialOrthogonalHom
        (source9NegativeCentral * g)) :
      Matrix Source48Label Source48Label ℝ) =
        ((source9SpinOriginalPaired48SpecialOrthogonalHom
            source9NegativeCentral) :
          Matrix Source48Label Source48Label ℝ) *
        ((source9SpinOriginalPaired48SpecialOrthogonalHom g) :
          Matrix Source48Label Source48Label ℝ) := by
            rw [map_mul]
            rfl
    _ = -(1 : Matrix Source48Label Source48Label ℝ) *
        ((source9SpinOriginalPaired48SpecialOrthogonalHom g) :
          Matrix Source48Label Source48Label ℝ) := by
            rw [source9NegativeCentral_originalPairedSO48_image]
    _ = -((source9SpinOriginalPaired48SpecialOrthogonalHom g) :
          Matrix Source48Label Source48Label ℝ) := by
            simp

/-- Right multiplication by the genuine source central
negative Clifford scalar has the same original-label sign
action, using source Spin9 centrality rather than an assumed
commutativity of the entire Spin9 group. -/
theorem source9NegativeCentral_originalPairedSO48_right_sign
    (g : spinGroup source9Quadratic) :
    ((source9SpinOriginalPaired48SpecialOrthogonalHom
        (g * source9NegativeCentral)) :
      Matrix Source48Label Source48Label ℝ) =
    -((source9SpinOriginalPaired48SpecialOrthogonalHom g) :
      Matrix Source48Label Source48Label ℝ) := by
  calc
    ((source9SpinOriginalPaired48SpecialOrthogonalHom
        (g * source9NegativeCentral)) :
      Matrix Source48Label Source48Label ℝ) =
        ((source9SpinOriginalPaired48SpecialOrthogonalHom
            (source9NegativeCentral * g)) :
          Matrix Source48Label Source48Label ℝ) := by
            rw [source9NegativeCentral_mul_comm g]
    _ = -((source9SpinOriginalPaired48SpecialOrthogonalHom g) :
          Matrix Source48Label Source48Label ℝ) :=
            source9NegativeCentral_originalPairedSO48_left_sign g

#print axioms source9NegativeCentral_sq_eq_one
#print axioms source9NegativeCentral_mul_comm
#print axioms source9NegativeCentral_originalPairedSO48_left_sign
#print axioms source9NegativeCentral_originalPairedSO48_right_sign

end
end FCP.BFSSPairedSpin9Clifford
