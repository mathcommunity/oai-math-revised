import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V37Original48CliffordGeneratorRankOneDeterminantProbe

/-!
K1D18A — candidate exact-source normalized polar-coordinate coefficient bridge.

This stage is only the original Fin 24 × Fin 2 finite-dimensional
polar-coefficient identity needed before comparing a Clifford generator's
actual vector action to the S1V37 rank-one determinant matrix.
It proves no arbitrary Spin-group determinant, parity, covering or spectrum.

Research candidate: independently strict qualification pending.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18A
noncomputable section

open FCP.BFSSS1V0
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Recover the actual original 48-vector from its original 48 coordinates. -/
theorem source48_coordinate_sum (a : Source48Vector) :
    (∑ j : Source48Label, (a j) • Pi.single j (1 : ℝ)) = a := by
  funext k
  simp [Pi.single_apply]

/-- For the true source quadratic form, the normalized polar coordinate row
evaluated on its own defining vector has exact dot product 2.
This is not yet a claim identifying a Clifford generator's conjugation action. -/
theorem source48_normalized_polar_coordinate_dot
    (a : Source48Vector) [Invertible (Q a)] :
    (fun j : Source48Label =>
      ⅟(Q a) * QuadraticMap.polar Q a (Pi.single j (1 : ℝ))) ⬝ᵥ a =
      (2 : ℝ) := by
  have hpolar :
      (∑ j : Source48Label,
        QuadraticMap.polar Q a (Pi.single j (1 : ℝ)) * a j) =
        QuadraticMap.polar Q a a := by
    calc
      _ = ∑ j : Source48Label,
            QuadraticMap.polar Q a ((a j) • Pi.single j (1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [QuadraticMap.polar_smul_right]
          simp only [smul_eq_mul]
          ring
      _ = QuadraticMap.polar Q a
            (∑ j : Source48Label, (a j) • Pi.single j (1 : ℝ)) := by
          simp only [← QuadraticMap.polarBilin_apply_apply, map_sum]
      _ = QuadraticMap.polar Q a a := by
          rw [source48_coordinate_sum]
  calc
    (fun j : Source48Label =>
      ⅟(Q a) * QuadraticMap.polar Q a (Pi.single j (1 : ℝ))) ⬝ᵥ a =
        ⅟(Q a) * (∑ j : Source48Label,
          QuadraticMap.polar Q a (Pi.single j (1 : ℝ)) * a j) := by
            simp only [dotProduct, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = ⅟(Q a) * QuadraticMap.polar Q a a := by rw [hpolar]
    _ = 2 := FCP.BFSSS1V37.source48_polar_inverse_self a

#print axioms source48_coordinate_sum
#print axioms source48_normalized_polar_coordinate_dot

end
end FCP.BFSSS1V52K1D18A
