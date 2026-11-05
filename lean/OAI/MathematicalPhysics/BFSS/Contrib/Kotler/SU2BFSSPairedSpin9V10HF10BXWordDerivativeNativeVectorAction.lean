import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BWFinitePlaneWordDerivative

/-!
F10BX — exact native vector action of the full ambient finite-word derivative.

Candidate only until strict compilation and independent PBW/type/axiom audit.
Reuse accepted BW's actual finite-word derivative and BL's half-bivector
commutator identity. Commutation on embedded source vectors yields the literal
sum of full native coordinate planes, with repetitions retained.

This gate is algebraic transport of a qualified ambient derivative. It does
not yet prove HasFDerivAt for the actual vector-action parameterization, a
native model isomorphism, a source tangent equivalence, an atlas or the full
group-map manifold differential.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSPairedSpin9Plane

local instance f10bxLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedAddCommGroup
local instance f10bxLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) :=
  source9PBWNormedSpace

/-- Coordinate evaluation times the literal full native plane applied to a fixed original vector. -/
noncomputable def source9PlaneParameterVectorVelocity {k : ℕ}
    (r s : SpaceIndex) (z : SpaceIndex → ℝ) (i : Fin k) :
    (Fin k → ℝ) →L[ℝ] (SpaceIndex → ℝ) :=
  (ContinuousLinearMap.toSpanSingleton ℝ ((coordinatePlane9 r s).mulVec z)).comp
    (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)

/-- The full native vector velocity is the listed sum of coordinate-plane evaluation maps. -/
noncomputable def source9PlaneWordVectorVelocity {k : ℕ}
    (r s : Fin k → SpaceIndex) (z : SpaceIndex → ℝ) :
    List (Fin k) → ((Fin k → ℝ) →L[ℝ] (SpaceIndex → ℝ))
  | [] => 0
  | i :: l => source9PlaneParameterVectorVelocity (r i) (s i) z i +
      source9PlaneWordVectorVelocity r s z l

/-- Evaluation is the literal finite sum of full native-plane actions in every direction. -/
theorem source9PlaneWordVectorVelocity_apply {k : ℕ}
    (r s : Fin k → SpaceIndex) (z : SpaceIndex → ℝ) (l : List (Fin k)) (v : Fin k → ℝ) :
    source9PlaneWordVectorVelocity r s z l v =
      (l.map (fun i => v i • ((coordinatePlane9 (r i) (s i)).mulVec z))).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [source9PlaneWordVectorVelocity, add_apply, List.map_cons, List.sum_cons]
      change v i • ((coordinatePlane9 (r i) (s i)).mulVec z) +
          source9PlaneWordVectorVelocity r s z l v =
        v i • ((coordinatePlane9 (r i) (s i)).mulVec z) +
          (l.map (fun j => v j • ((coordinatePlane9 (r j) (s j)).mulVec z))).sum
      rw [ih]

/-- The full source half-bivector sum commutes on vectors by the full native-plane sum. -/
theorem source9PlaneSpinWordVelocity_commutator_vector {k : ℕ}
    (r s : Fin k → SpaceIndex) (l : List (Fin k)) (v : Fin k → ℝ)
    (z : SpaceIndex → ℝ) :
    source9PlaneSpinWordVelocity r s l v * CliffordAlgebra.ι source9Quadratic z -
      CliffordAlgebra.ι source9Quadratic z * source9PlaneSpinWordVelocity r s l v =
        CliffordAlgebra.ι source9Quadratic (source9PlaneWordVectorVelocity r s z l v) := by
  induction l with
  | nil =>
      change (0 : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z -
        CliffordAlgebra.ι source9Quadratic z * 0 =
          CliffordAlgebra.ι source9Quadratic (0 : SpaceIndex → ℝ)
      simp only [zero_mul, mul_zero, sub_self, map_zero]
  | cons i l ih =>
      have hhead :
          source9PlaneParameterVelocity (r i) (s i) i v *
              CliffordAlgebra.ι source9Quadratic z -
            CliffordAlgebra.ι source9Quadratic z *
              source9PlaneParameterVelocity (r i) (s i) i v =
            CliffordAlgebra.ι source9Quadratic
              (source9PlaneParameterVectorVelocity (r i) (s i) z i v) := by
        change
          (v i • ((1 / 2 : ℝ) •
            (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (r i)) *
              CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (s i))))) *
                CliffordAlgebra.ι source9Quadratic z -
            CliffordAlgebra.ι source9Quadratic z *
              (v i • ((1 / 2 : ℝ) •
                (CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (r i)) *
                  CliffordAlgebra.ι source9Quadratic (source9CoordinateVector (s i))))) =
            CliffordAlgebra.ι source9Quadratic
              (v i • ((coordinatePlane9 (r i) (s i)).mulVec z))
        rw [smul_mul_assoc, mul_smul_comm, ← smul_sub,
          source9CoordinateBivector_commutator_vector, map_smul]
      change
        (source9PlaneParameterVelocity (r i) (s i) i v +
          source9PlaneSpinWordVelocity r s l v) * CliffordAlgebra.ι source9Quadratic z -
          CliffordAlgebra.ι source9Quadratic z *
            (source9PlaneParameterVelocity (r i) (s i) i v +
              source9PlaneSpinWordVelocity r s l v) =
        CliffordAlgebra.ι source9Quadratic
          (source9PlaneParameterVectorVelocity (r i) (s i) z i v +
            source9PlaneWordVectorVelocity r s z l v)
      rw [add_mul, mul_add, map_add]
      calc
        _ =
            (source9PlaneParameterVelocity (r i) (s i) i v *
                CliffordAlgebra.ι source9Quadratic z -
              CliffordAlgebra.ι source9Quadratic z *
                source9PlaneParameterVelocity (r i) (s i) i v) +
            (source9PlaneSpinWordVelocity r s l v * CliffordAlgebra.ι source9Quadratic z -
              CliffordAlgebra.ι source9Quadratic z * source9PlaneSpinWordVelocity r s l v) := by
          abel
        _ = _ := by rw [hhead, ih]

/-- The accepted canonical projection recovers the exact native vector sum from that commutator. -/
theorem source9PlaneSpinWordVelocity_projected_commutator {k : ℕ}
    (r s : Fin k → SpaceIndex) (l : List (Fin k)) (v : Fin k → ℝ)
    (z : SpaceIndex → ℝ) :
    source9CliffordVectorProjection
      (source9PlaneSpinWordVelocity r s l v * CliffordAlgebra.ι source9Quadratic z -
        CliffordAlgebra.ι source9Quadratic z * source9PlaneSpinWordVelocity r s l v) =
      source9PlaneWordVectorVelocity r s z l v := by
  rw [source9PlaneSpinWordVelocity_commutator_vector, source9CliffordVectorProjection_ι]

/-- Tie the algebraic transport to the literal actual-word fderiv, not only a velocity wrapper. -/
theorem source9PlaneSpinWord_fderiv_projected_commutator {k : ℕ}
    (r s : Fin k → SpaceIndex) (hrs : ∀ i, r i ≠ s i) (l : List (Fin k))
    (v : Fin k → ℝ) (z : SpaceIndex → ℝ) :
    source9CliffordVectorProjection
      (((fderiv ℝ (fun t : Fin k → ℝ =>
          ((source9PlaneSpinWord r s hrs t l) : CliffordAlgebra source9Quadratic)) 0) v) *
            CliffordAlgebra.ι source9Quadratic z -
        CliffordAlgebra.ι source9Quadratic z *
          ((fderiv ℝ (fun t : Fin k → ℝ =>
            ((source9PlaneSpinWord r s hrs t l) : CliffordAlgebra source9Quadratic)) 0) v)) =
      source9PlaneWordVectorVelocity r s z l v := by
  have hmap :
      fderiv ℝ (fun t : Fin k → ℝ =>
        ((source9PlaneSpinWord r s hrs t l) : CliffordAlgebra source9Quadratic)) 0 =
        source9PlaneSpinWordVelocity r s l :=
    source9PlaneSpinWord_coe_fderiv_zero r s hrs l
  have hvalue :
      (fderiv ℝ (fun t : Fin k → ℝ =>
        ((source9PlaneSpinWord r s hrs t l) : CliffordAlgebra source9Quadratic)) 0) v =
        source9PlaneSpinWordVelocity r s l v :=
    congrArg (fun L : (Fin k → ℝ) →L[ℝ] CliffordAlgebra source9Quadratic => L v) hmap
  exact (congrArg (fun a : CliffordAlgebra source9Quadratic =>
    source9CliffordVectorProjection
      (a * CliffordAlgebra.ι source9Quadratic z - CliffordAlgebra.ι source9Quadratic z * a))
    hvalue).trans (source9PlaneSpinWordVelocity_projected_commutator r s l v z)

#print axioms source9PlaneParameterVectorVelocity
#print axioms source9PlaneWordVectorVelocity
#print axioms source9PlaneWordVectorVelocity_apply
#print axioms source9PlaneSpinWordVelocity_commutator_vector
#print axioms source9PlaneSpinWordVelocity_projected_commutator
#print axioms source9PlaneSpinWord_fderiv_projected_commutator

end
end FCP.BFSSPairedSpin9Clifford
