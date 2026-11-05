import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10SOriginalPairedNegativeScalarActionProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
K1D18V10H-F10T — actual negative central scalar membership in
the GENUINE Mathlib source spinGroup source9Quadratic.

Reuse the accepted original Spin48 K1D9 structural proof method:
construct -1 as the product of opposite source-unit Clifford
generators and show actual Lipschitz membership, unitarity and
evenness. Here the vector and form are EXACTLY the source nine-
dimensional SpaceIndex / source9Quadratic, not a 48-dimensional
replacement. Do not expand Lipschitz closure by definitional
reduction, which historically exhausted elaboration resources.

This candidate constructs the actual source Spin9 element;
it does not yet prove its SO48 matrix action or its exact
kernel relation, continuous homomorphism, original Spin48
lift/cover, Fock implementation or BFSS spectrum.

CANDIDATE until strict original-source compilation and
independent four-declaration exact type and axiom gate.
No heartbeat/recursion-limit increase.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum

private abbrev Q : QuadraticForm ℝ (SpaceIndex → ℝ) := source9Quadratic
private abbrev C := CliffordAlgebra Q

/-- For an ACTUAL source nine-vector of Q-norm one,
the original negative Clifford scalar belongs to source Spin9. -/
theorem source9_neg_one_mem_of_unitVector
    (v : SpaceIndex → ℝ) (hv : Q v = 1) :
    (-1 : C) ∈ spinGroup Q := by
  have hsq : CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v = 1 := by
    simpa only [hv, map_one] using (CliffordAlgebra.ι_sq_scalar Q v)
  have hsqNeg : CliffordAlgebra.ι Q (-v) * CliffordAlgebra.ι Q (-v) = 1 := by
    simpa only [map_neg, neg_mul_neg] using hsq
  let u : Cˣ :=
    ⟨CliffordAlgebra.ι Q v, CliffordAlgebra.ι Q v, hsq, hsq⟩
  let w : Cˣ :=
    ⟨CliffordAlgebra.ι Q (-v), CliffordAlgebra.ι Q (-v), hsqNeg, hsqNeg⟩
  have hu : u ∈ lipschitzGroup Q := by
    exact Subgroup.subset_closure
      (show (u : C) ∈ Set.range (CliffordAlgebra.ι Q) from ⟨v, rfl⟩)
  have hw : w ∈ lipschitzGroup Q := by
    exact Subgroup.subset_closure
      (show (w : C) ∈ Set.range (CliffordAlgebra.ι Q) from ⟨-v, rfl⟩)
  have hneg : ((u * w : Cˣ) : C) = -1 := by
    change CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q (-v) = -1
    rw [map_neg, mul_neg, hsq]
  have hunit : (-1 : C) ∈ unitary C := by
    change star (-1 : C) * (-1 : C) = 1 ∧
      (-1 : C) * star (-1 : C) = 1
    constructor <;> simp
  have hpin : (-1 : C) ∈ pinGroup Q := by
    rw [← hneg]
    exact (pinGroup.units_mem_iff).2 ⟨mul_mem hu hw, by simpa only [hneg] using hunit⟩
  have heven : (-1 : C) ∈ CliffordAlgebra.even Q := by
    exact (CliffordAlgebra.even Q).neg_mem (CliffordAlgebra.even Q).one_mem
  exact (spinGroup.mem_iff).2 ⟨hpin, heven⟩

/-- The EXACT source nine-coordinate quadratic form has a
unit coordinate vector, so -1 belongs to genuine source Spin9. -/
theorem source9_neg_one_mem :
    (-1 : CliffordAlgebra source9Quadratic) ∈
      spinGroup source9Quadratic := by
  let v : SpaceIndex → ℝ :=
    fun i => if i = (0 : SpaceIndex) then 1 else 0
  have hv : Q v = 1 := by
    simp [source9Quadratic, QuadraticMap.weightedSumSquares_apply, v]
  exact source9_neg_one_mem_of_unitVector v hv

/-- Source-exact genuine negative central Spin9 element;
this is NOT a substitute abstract group or physical model. -/
noncomputable def source9NegativeCentral :
    spinGroup source9Quadratic :=
  ⟨-1, source9_neg_one_mem⟩

/-- The original underlying Clifford element is exactly -1. -/
theorem source9NegativeCentral_coe :
    ((source9NegativeCentral : spinGroup source9Quadratic) :
      CliffordAlgebra source9Quadratic) = -1 := rfl

#print axioms source9_neg_one_mem_of_unitVector
#print axioms source9_neg_one_mem
#print axioms source9NegativeCentral
#print axioms source9NegativeCentral_coe

end
end FCP.BFSSPairedSpin9Clifford
