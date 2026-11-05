import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BICoordinatePlaneSourceCurve
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9CoordinateMatrixUnitBridgeProbe

/-!
F10BL — algebraic action of source half-bivectors on actual source vectors.

Candidate only until the strict compiler and independent type/axiom audit pass.
Use the existing source9Quadratic, source9CoordinateVector, Clifford embedding,
and literal coordinatePlane9 = E_rs - E_sr. The final identity is an equality
inside the actual source Clifford algebra for every original source vector.

This gate proves a commutator identity, not a derivative of the source group
conjugation action, a manifold tangent identification, or a global differential
theorem. The identity may include diagonal labels without extending the
distinct-plane source curve to the diagonal.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSPairedSpin9Plane

/-- The actual source quadratic polarization against a coordinate vector is twice that coordinate. -/
theorem source9Quadratic_polar_coordinate (r : SpaceIndex) (z : SpaceIndex → ℝ) :
    QuadraticMap.polar source9Quadratic (source9CoordinateVector r) z = 2 * z r := by
  simp only [QuadraticMap.polar, source9Quadratic_eq_dot, add_dotProduct, dotProduct_add]
  simp only [source9CoordinateVector, single_dotProduct, dotProduct_single,
    Pi.single_eq_same, one_mul, mul_one]
  ring

/-- A Clifford vector-pair commutator is determined by the actual source polarization. -/
theorem source9Clifford_pair_commutator_vector
    (u v w : SpaceIndex → ℝ) :
    (CliffordAlgebra.ι source9Quadratic u * CliffordAlgebra.ι source9Quadratic v) *
        CliffordAlgebra.ι source9Quadratic w -
      CliffordAlgebra.ι source9Quadratic w *
        (CliffordAlgebra.ι source9Quadratic u * CliffordAlgebra.ι source9Quadratic v) =
      (QuadraticMap.polar source9Quadratic v w) • CliffordAlgebra.ι source9Quadratic u -
        (QuadraticMap.polar source9Quadratic w u) • CliffordAlgebra.ι source9Quadratic v := by
  calc
    _ = CliffordAlgebra.ι source9Quadratic u *
          (algebraMap ℝ (CliffordAlgebra source9Quadratic)
              (QuadraticMap.polar source9Quadratic v w) -
            CliffordAlgebra.ι source9Quadratic w * CliffordAlgebra.ι source9Quadratic v) -
        (algebraMap ℝ (CliffordAlgebra source9Quadratic)
            (QuadraticMap.polar source9Quadratic w u) -
          CliffordAlgebra.ι source9Quadratic u * CliffordAlgebra.ι source9Quadratic w) *
            CliffordAlgebra.ι source9Quadratic v := by
      rw [mul_assoc,
        ← mul_assoc (CliffordAlgebra.ι source9Quadratic w)
          (CliffordAlgebra.ι source9Quadratic u) (CliffordAlgebra.ι source9Quadratic v),
        CliffordAlgebra.ι_mul_ι_comm v w, CliffordAlgebra.ι_mul_ι_comm w u]
    _ = _ := by
      simp only [mul_sub, sub_mul, Algebra.algebraMap_eq_smul_one,
        mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc]
      abel

/-- The literal native source plane acts on every vector by its two original coordinates. -/
theorem source9CoordinatePlane_mulVec
    (r s : SpaceIndex) (z : SpaceIndex → ℝ) :
    (coordinatePlane9 r s).mulVec z =
      (z s) • source9CoordinateVector r - (z r) • source9CoordinateVector s := by
  have sum_guarded_coordinate (p : Prop) [Decidable p] (j : SpaceIndex) :
      (∑ x : SpaceIndex, if p ∧ x = j then z x else 0) =
        if p then z j else 0 := by
    by_cases hp : p <;> simp [hp]
  ext i
  by_cases hir : i = r <;> by_cases his : i = s <;>
    simp [coordinatePlane9, Matrix.mulVec, dotProduct, source9CoordinateVector,
      Pi.single_apply, hir, his, sub_mul, Finset.sum_sub_distrib, ite_mul, smul_eq_mul]
  all_goals exact sum_guarded_coordinate _ _

/-- Commutation by the actual source half-bivector implements the unchanged native plane on vectors. -/
theorem source9CoordinateBivector_commutator_vector
    (r s : SpaceIndex) (z : SpaceIndex → ℝ) :
    ((1 / 2 : ℝ) •
        (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
          CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))) *
        CliffordAlgebra.ι source9Quadratic z -
      CliffordAlgebra.ι source9Quadratic z *
        ((1 / 2 : ℝ) •
          (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
            CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))) =
      CliffordAlgebra.ι source9Quadratic ((coordinatePlane9 r s).mulVec z) := by
  have h := source9Clifford_pair_commutator_vector
    (source9CoordinateVector r) (source9CoordinateVector s) z
  rw [source9Quadratic_polar_coordinate s z,
    QuadraticMap.polar_comm source9Quadratic z (source9CoordinateVector r),
    source9Quadratic_polar_coordinate r z] at h
  rw [source9CoordinatePlane_mulVec, map_sub, map_smul, map_smul]
  calc
    _ = (1 / 2 : ℝ) •
        ((CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
            CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s)) *
            CliffordAlgebra.ι source9Quadratic z -
          CliffordAlgebra.ι source9Quadratic z *
            (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) *
              CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s))) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_sub]
    _ = (1 / 2 : ℝ) •
        ((2 * z s) • CliffordAlgebra.ι source9Quadratic (source9CoordinateVector r) -
          (2 * z r) • CliffordAlgebra.ι source9Quadratic (source9CoordinateVector s)) := by
      rw [h]
    _ = _ := by
      have hs : (1 / 2 : ℝ) * (2 * z s) = z s := by ring
      have hr : (1 / 2 : ℝ) * (2 * z r) = z r := by ring
      rw [smul_sub, smul_smul, smul_smul, hs, hr]

#print axioms source9Quadratic_polar_coordinate
#print axioms source9Clifford_pair_commutator_vector
#print axioms source9CoordinatePlane_mulVec
#print axioms source9CoordinateBivector_commutator_vector

end
end FCP.BFSSPairedSpin9Clifford
