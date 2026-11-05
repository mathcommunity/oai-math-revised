import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9NormalizedFourIndexStructureProbe

/-!
K1D18V8S — first exact typed nine-dimensional INPUT carrier for a
potential so(9) → so(48) algebra map.

F_rs := E_rs - E_sr is defined entrywise on the actual SpaceIndex.
This is a 9×9 coordinate plane, NOT a 48-label source matrix.
The original paired 48-real normalized H_rs remains separate in V8R.

Prove only input diagonal zero, orientation reversal, and skew
transpose. Neither generator-bracket compatibility nor any linear
or Lie algebra homomorphism is asserted here.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum

/-- Explicit 9×9 skew coordinate plane E_rs - E_sr over native SpaceIndex. -/
noncomputable def coordinatePlane9 (r s : SpaceIndex) :
    Matrix SpaceIndex SpaceIndex ℝ :=
  fun i j =>
    (if i = r ∧ j = s then (1 : ℝ) else 0) -
    (if i = s ∧ j = r then (1 : ℝ) else 0)

/-- Input coordinate plane is zero on the diagonal r=s. -/
theorem coordinatePlane9_self (r : SpaceIndex) :
    coordinatePlane9 r r = 0 := by
  ext i j
  simp [coordinatePlane9]

/-- Input coordinate plane reverses sign under exchanging its labels. -/
theorem coordinatePlane9_swap (r s : SpaceIndex) :
    coordinatePlane9 s r = -(coordinatePlane9 r s) := by
  ext i j
  change
    ((if i = s ∧ j = r then (1 : ℝ) else 0) -
       (if i = r ∧ j = s then (1 : ℝ) else 0)) =
    -((if i = r ∧ j = s then (1 : ℝ) else 0) -
       (if i = s ∧ j = r then (1 : ℝ) else 0))
  abel

/-- Every source-native nine-dimensional coordinate plane is skew. -/
theorem coordinatePlane9_transpose (r s : SpaceIndex) :
    (coordinatePlane9 r s).transpose = -(coordinatePlane9 r s) := by
  ext i j
  change
    ((if j = r ∧ i = s then (1 : ℝ) else 0) -
       (if j = s ∧ i = r then (1 : ℝ) else 0)) =
    -((if i = r ∧ j = s then (1 : ℝ) else 0) -
       (if i = s ∧ j = r then (1 : ℝ) else 0))
  -- Simplification is congruence-aware inside dependent ite conditions.
  simp only [and_comm]
  abel

#print axioms coordinatePlane9_self
#print axioms coordinatePlane9_swap
#print axioms coordinatePlane9_transpose

end
end FCP.BFSSPairedSpin9Plane
