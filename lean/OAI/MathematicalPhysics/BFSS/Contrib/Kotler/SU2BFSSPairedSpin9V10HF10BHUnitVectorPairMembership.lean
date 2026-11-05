import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BCSourceSpinGammaSpecialOrthogonalHom
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
F10BH — normalized source vector pairs in the exact algebraic Spin9 group.

Candidate prerequisite for a future coordinate-plane source curve.
The source vectors have the existing positive source9Quadratic norm one.
A single such Clifford vector squares to one but its Clifford star is
its negative. No membership of an individual vector in pinGroup is asserted.

For a pair, the two star signs cancel. Membership is proved in the actual
generated Lipschitz group, the actual unitary submonoid, and the even
Clifford subalgebra. The original gamma image is then identified exactly.
No curve, derivative, manifold, Lie-group atlas or differential comparison
is claimed by this algebraic prerequisite.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum

/-- A normalized actual source vector gives a self-inverse Clifford unit. -/
noncomputable def source9UnitVectorCliffordUnit
    (v : SpaceIndex → ℝ) (hv : source9Quadratic v = 1) :
    (CliffordAlgebra source9Quadratic)ˣ where
  val := CliffordAlgebra.ι source9Quadratic v
  inv := CliffordAlgebra.ι source9Quadratic v
  val_inv := by rw [CliffordAlgebra.ι_sq_scalar, hv, map_one]
  inv_val := by rw [CliffordAlgebra.ι_sq_scalar, hv, map_one]

/-- This exact unit is one of the generators of the pinned Lipschitz group. -/
theorem source9UnitVectorCliffordUnit_mem_lipschitzGroup
    (v : SpaceIndex → ℝ) (hv : source9Quadratic v = 1) :
    source9UnitVectorCliffordUnit v hv ∈ lipschitzGroup source9Quadratic := by
  unfold lipschitzGroup
  apply Subgroup.subset_closure
  exact ⟨v, rfl⟩

/-- Every pair of normalized actual source vectors has Clifford product in the actual Spin9 group. -/
theorem source9UnitVectorPair_mem_spinGroup
    (u v : SpaceIndex → ℝ)
    (hu : source9Quadratic u = 1) (hv : source9Quadratic v = 1) :
    CliffordAlgebra.ι source9Quadratic u * CliffordAlgebra.ι source9Quadratic v ∈
      spinGroup source9Quadratic := by
  have hu2 : CliffordAlgebra.ι source9Quadratic u *
      CliffordAlgebra.ι source9Quadratic u = 1 := by
    rw [CliffordAlgebra.ι_sq_scalar, hu, map_one]
  have hv2 : CliffordAlgebra.ι source9Quadratic v *
      CliffordAlgebra.ι source9Quadratic v = 1 := by
    rw [CliffordAlgebra.ι_sq_scalar, hv, map_one]
  rw [spinGroup.mem_iff, pinGroup.mem_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Submonoid.mem_map]
    refine ⟨source9UnitVectorCliffordUnit u hu * source9UnitVectorCliffordUnit v hv, ?_, rfl⟩
    exact (lipschitzGroup source9Quadratic).mul_mem
      (source9UnitVectorCliffordUnit_mem_lipschitzGroup u hu)
      (source9UnitVectorCliffordUnit_mem_lipschitzGroup v hv)
  · constructor
    · simp only [star_mul, CliffordAlgebra.star_ι, neg_mul_neg]
      calc
        (CliffordAlgebra.ι source9Quadratic v * CliffordAlgebra.ι source9Quadratic u) *
            (CliffordAlgebra.ι source9Quadratic u * CliffordAlgebra.ι source9Quadratic v) =
            CliffordAlgebra.ι source9Quadratic v *
              (CliffordAlgebra.ι source9Quadratic u * CliffordAlgebra.ι source9Quadratic u) *
                CliffordAlgebra.ι source9Quadratic v := by simp only [mul_assoc]
        _ = 1 := by rw [hu2, mul_one, hv2]
    · simp only [star_mul, CliffordAlgebra.star_ι, neg_mul_neg]
      calc
        (CliffordAlgebra.ι source9Quadratic u * CliffordAlgebra.ι source9Quadratic v) *
            (CliffordAlgebra.ι source9Quadratic v * CliffordAlgebra.ι source9Quadratic u) =
            CliffordAlgebra.ι source9Quadratic u *
              (CliffordAlgebra.ι source9Quadratic v * CliffordAlgebra.ι source9Quadratic v) *
                CliffordAlgebra.ι source9Quadratic u := by simp only [mul_assoc]
        _ = 1 := by rw [hv2, mul_one, hu2]
  · exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero source9Quadratic u v

/-- The normalized vector pair as an element of the exact source Spin9 carrier. -/
noncomputable def source9UnitVectorPairSpin
    (u v : SpaceIndex → ℝ)
    (hu : source9Quadratic u = 1) (hv : source9Quadratic v = 1) :
    spinGroup source9Quadratic :=
  ⟨CliffordAlgebra.ι source9Quadratic u * CliffordAlgebra.ι source9Quadratic v,
    source9UnitVectorPair_mem_spinGroup u v hu hv⟩

/-- The exact F10BC image is the product of the original source gamma evaluations. -/
theorem source9UnitVectorPairSpin_gamma
    (u v : SpaceIndex → ℝ)
    (hu : source9Quadratic u = 1) (hv : source9Quadratic v = 1) :
    ((source9SpinGammaSpecialOrthogonalHom (source9UnitVectorPairSpin u v hu hv)) :
      GammaMatrix) = gammaNineRealLinear u * gammaNineRealLinear v := by
  rw [source9SpinGammaSpecialOrthogonalHom_apply]
  change source9GammaCliffordAlgHom
      (CliffordAlgebra.ι source9Quadratic u * CliffordAlgebra.ι source9Quadratic v) =
    gammaNineRealLinear u * gammaNineRealLinear v
  rw [map_mul, source9GammaCliffordAlgHom_generator, source9GammaCliffordAlgHom_generator]

#print axioms source9UnitVectorCliffordUnit
#print axioms source9UnitVectorCliffordUnit_mem_lipschitzGroup
#print axioms source9UnitVectorPair_mem_spinGroup
#print axioms source9UnitVectorPairSpin
#print axioms source9UnitVectorPairSpin_gamma

end
end FCP.BFSSPairedSpin9Clifford
