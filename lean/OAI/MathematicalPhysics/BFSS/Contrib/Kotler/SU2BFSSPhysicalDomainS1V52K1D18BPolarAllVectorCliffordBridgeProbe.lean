import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18APolarCoordinateNormalizationProbe

/-!
K1D18B — source-exact original 48-coordinate normalized polar row,
for EVERY source input vector, and its equality with genuine original
Clifford degree-one generator conjugation.

This does not yet identify an actual generator with the rank-one matrix,
admit determinant +1 on Spin48, prove a Lipschitz closure-parity bridge,
or prove any global group covering/physical BFSS statement.

Candidate, pending strict fresh compilation and axiom audit.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18B
noncomputable section

open FCP.BFSSS1V0
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- The original source 48-coordinates of the normalized polar functional. -/
noncomputable def source48NormalizedPolarRow
    (a : Source48Vector) [Invertible (Q a)] : Source48Vector :=
  fun j => ⅟(Q a) * QuadraticMap.polar Q a (Pi.single j (1 : ℝ))

/-- Normalized polar evaluation is literally the source row dot product
on every ORIGINAL source vector, with no surrogate basis or form. -/
theorem source48NormalizedPolarRow_dot
    (a b : Source48Vector) [Invertible (Q a)] :
    source48NormalizedPolarRow a ⬝ᵥ b =
      ⅟(Q a) * QuadraticMap.polar Q a b := by
  have hpolar :
      (∑ j : Source48Label,
        QuadraticMap.polar Q a (Pi.single j (1 : ℝ)) * b j) =
        QuadraticMap.polar Q a b := by
    calc
      _ = ∑ j : Source48Label,
            QuadraticMap.polar Q a ((b j) • Pi.single j (1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [QuadraticMap.polar_smul_right]
          simp only [smul_eq_mul]
          ring
      _ = QuadraticMap.polar Q a
            (∑ j : Source48Label, (b j) • Pi.single j (1 : ℝ)) := by
          simp only [← QuadraticMap.polarBilin_apply_apply, map_sum]
      _ = QuadraticMap.polar Q a b := by
          rw [FCP.BFSSS1V52K1D18A.source48_coordinate_sum]
  calc
    source48NormalizedPolarRow a ⬝ᵥ b =
      ⅟(Q a) * (∑ j : Source48Label,
        QuadraticMap.polar Q a (Pi.single j (1 : ℝ)) * b j) := by
          simp only [source48NormalizedPolarRow, dotProduct, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ⅟(Q a) * QuadraticMap.polar Q a b := by rw [hpolar]

/-- The exact original row dot its defining vector is 2. -/
theorem source48NormalizedPolarRow_dot_self
    (a : Source48Vector) [Invertible (Q a)] :
    source48NormalizedPolarRow a ⬝ᵥ a = (2 : ℝ) := by
  change (fun j : Source48Label =>
    ⅟(Q a) * QuadraticMap.polar Q a (Pi.single j (1 : ℝ))) ⬝ᵥ a = 2
  exact FCP.BFSSS1V52K1D18A.source48_normalized_polar_coordinate_dot a

/-- The actual original Clifford generator conjugation is the
normalized source 48-coordinate row contraction, not a guessed
matrix action. The matrix realization remains a separate step. -/
theorem source48_clifford_generator_conjugation_from_row
    (a b : Source48Vector)
    [Invertible (CliffordAlgebra.ι Q a)] [Invertible (Q a)] :
    CliffordAlgebra.ι Q
      ((source48NormalizedPolarRow a ⬝ᵥ b) • a - b) =
        CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b *
          ⅟(CliffordAlgebra.ι Q a) := by
  rw [source48NormalizedPolarRow_dot]
  exact FCP.BFSSS1V37.source48_clifford_generator_conjugation a b

#print axioms source48NormalizedPolarRow_dot
#print axioms source48NormalizedPolarRow_dot_self
#print axioms source48_clifford_generator_conjugation_from_row

end
end FCP.BFSSS1V52K1D18B
