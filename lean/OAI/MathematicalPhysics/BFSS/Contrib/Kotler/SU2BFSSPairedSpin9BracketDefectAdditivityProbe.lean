import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9GeneratorCommutatorPreservationProbe

/-!
K1D18V9I — native, exactly typed additivity of the generator
commutator-preservation defect in both input matrix arguments.

The defect is formed from the actual real 9×9 source matrix product
commutator and actual original Fock-paired 48×48 output matrix
product commutator. This is not defined as an abstract Lie bracket.

This stage establishes additive transport in each argument for
arbitrary source matrices. Its value on pairs of coordinate planes
vanishes by the accepted V9H theorem, but scalar homogeneity and
arbitrary skew-input bracket preservation remain separate gates.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- The exact original paired 48-real failure of the real linear
coefficient map to preserve native 9×9 matrix commutators. -/
noncomputable def coordinateToPairedBracketDefect
    (A B : Matrix SpaceIndex SpaceIndex ℝ) :
    Matrix Source48Label Source48Label ℝ :=
  coordinateToPairedLinearMap (A * B - B * A) -
    (coordinateToPairedLinearMap A * coordinateToPairedLinearMap B -
     coordinateToPairedLinearMap B * coordinateToPairedLinearMap A)

/-- Additivity of the exact bracket-preservation defect in its
first native nine-index matrix argument. -/
theorem coordinateToPairedBracketDefect_add_left
    (A B C : Matrix SpaceIndex SpaceIndex ℝ) :
    coordinateToPairedBracketDefect (A + B) C =
      coordinateToPairedBracketDefect A C +
      coordinateToPairedBracketDefect B C := by
  unfold coordinateToPairedBracketDefect
  simp only [add_mul, mul_add, map_add, map_sub]
  abel

/-- Additivity of the exact bracket-preservation defect in its
second native nine-index matrix argument. -/
theorem coordinateToPairedBracketDefect_add_right
    (A B C : Matrix SpaceIndex SpaceIndex ℝ) :
    coordinateToPairedBracketDefect A (B + C) =
      coordinateToPairedBracketDefect A B +
      coordinateToPairedBracketDefect A C := by
  unfold coordinateToPairedBracketDefect
  simp only [add_mul, mul_add, map_add, map_sub]
  abel

#print axioms coordinateToPairedBracketDefect_add_left
#print axioms coordinateToPairedBracketDefect_add_right

end
end FCP.BFSSPairedSpin9Plane
