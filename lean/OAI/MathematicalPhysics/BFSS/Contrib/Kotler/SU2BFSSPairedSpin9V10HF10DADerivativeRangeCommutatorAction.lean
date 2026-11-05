import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CZOriginalGammaDerivativeRangeComparison
import Mathlib.Tactic.NoncommRing

/-! F10DA: exact vector action of the actual derivative range and its commutators.
Reuse CY's literal range/native equivalence, BX's original Clifford vector action and CZ's
original-gamma comparison. Reduce commutator closure to exact native bracket compatibility.
No range Lie algebra, closure theorem, source tangent identification or manifold differential
is assumed or asserted. Candidate until fresh strict compilation and independent audit. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Plane
open scoped Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

local instance f10daLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) := source9PBWNormedAddCommGroup
local instance f10daLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) := source9PBWNormedSpace

private theorem listed_vector_velocity_mulVec {k : ℕ}
    (r s : Fin k → SpaceIndex) (l : List (Fin k)) (v : Fin k → ℝ) (z : SpaceIndex → ℝ) :
    source9PlaneWordVectorVelocity r s z l v =
      ((l.map (fun i => v i • coordinatePlane9 (r i) (s i))).sum).mulVec z := by
  induction l with
  | nil =>
      change (0 : SpaceIndex → ℝ) = (0 : Matrix SpaceIndex SpaceIndex ℝ).mulVec z
      exact (Matrix.zero_mulVec z).symm
  | cons i l ih =>
      simp only [source9PlaneWordVectorVelocity, add_apply, List.map_cons, List.sum_cons,
        Matrix.add_mulVec, Matrix.smul_mulVec]
      change v i • ((coordinatePlane9 (r i) (s i)).mulVec z) +
          source9PlaneWordVectorVelocity r s z l v =
        v i • ((coordinatePlane9 (r i) (s i)).mulVec z) +
          ((l.map (fun j => v j • coordinatePlane9 (r j) (s j))).sum).mulVec z
      rw [ih]

/-- Every full vector velocity is the accepted native model acting on that original vector. -/
theorem source9OrderedStrictPlaneVectorVelocity_model (v : Fin 36 → ℝ) (z : SpaceIndex → ℝ) :
    source9PlaneWordVectorVelocity source9StrictPlaneRow source9StrictPlaneColumn
      z (List.finRange 36) v =
        (source9OrderedStrictPlaneModelEquiv v : Matrix SpaceIndex SpaceIndex ℝ).mulVec z :=
  (listed_vector_velocity_mulVec source9StrictPlaneRow source9StrictPlaneColumn
    (List.finRange 36) v z).trans
      (congrArg (fun M : Matrix SpaceIndex SpaceIndex ℝ => M.mulVec z)
        (source9OrderedStrictPlane_sum_eq_model v))

/-- The actual native range representative acts on all embedded vectors, before projection. -/
theorem source9NativeSkewDerivativeRangeEquiv_commutator_vector
    (A : LieAlgebra.Orthogonal.so SpaceIndex ℝ) (z : SpaceIndex → ℝ) :
    (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
        CliffordAlgebra.ι source9Quadratic z -
      CliffordAlgebra.ι source9Quadratic z *
        (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) =
      CliffordAlgebra.ι source9Quadratic (A.val.mulVec z) := by
  let v : Fin 36 → ℝ := source9OrderedStrictPlaneModelEquiv.symm A
  have hL : source9IdentityChartDerivative =
      source9PlaneSpinWordVelocity source9StrictPlaneRow source9StrictPlaneColumn (List.finRange 36) :=
    source9IdentityChartInverse_clifford_fderiv_zero
  have hvalue : (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) =
      source9PlaneSpinWordVelocity source9StrictPlaneRow source9StrictPlaneColumn (List.finRange 36) v :=
    (source9NativeSkewDerivativeRangeEquiv_apply A).trans
      (congrArg (fun D : (Fin 36 → ℝ) →L[ℝ] CliffordAlgebra source9Quadratic => D v) hL)
  have hmatrix : (source9OrderedStrictPlaneModelEquiv v : Matrix SpaceIndex SpaceIndex ℝ) = A.val :=
    congrArg (fun B : LieAlgebra.Orthogonal.so SpaceIndex ℝ => B.val)
      (source9OrderedStrictPlaneModelEquiv.apply_symm_apply A)
  have hvector : source9PlaneWordVectorVelocity source9StrictPlaneRow source9StrictPlaneColumn
      z (List.finRange 36) v = A.val.mulVec z :=
    (source9OrderedStrictPlaneVectorVelocity_model v z).trans
      (congrArg (fun M : Matrix SpaceIndex SpaceIndex ℝ => M.mulVec z) hmatrix)
  exact (congrArg (fun a : CliffordAlgebra source9Quadratic =>
    a * CliffordAlgebra.ι source9Quadratic z - CliffordAlgebra.ι source9Quadratic z * a) hvalue).trans
      ((source9PlaneSpinWordVelocity_commutator_vector source9StrictPlaneRow source9StrictPlaneColumn
        (List.finRange 36) v z).trans (congrArg (CliffordAlgebra.ι source9Quadratic) hvector))

/-- All actual range values have the full native vector action of their inverse coordinates. -/
theorem source9DerivativeRange_commutator_vector
    (x : source9IdentityChartDerivativeRange) (z : SpaceIndex → ℝ) :
    (x : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z -
      CliffordAlgebra.ι source9Quadratic z * (x : CliffordAlgebra source9Quadratic) =
      CliffordAlgebra.ι source9Quadratic
        ((source9NativeSkewDerivativeRangeEquiv.symm x).val.mulVec z) := by
  have hvalue : (source9NativeSkewDerivativeRangeEquiv (source9NativeSkewDerivativeRangeEquiv.symm x) :
      CliffordAlgebra source9Quadratic) = (x : CliffordAlgebra source9Quadratic) :=
    congrArg (fun y : source9IdentityChartDerivativeRange => (y : CliffordAlgebra source9Quadratic))
      (source9NativeSkewDerivativeRangeEquiv.apply_symm_apply x)
  exact (congrArg (fun a : CliffordAlgebra source9Quadratic =>
    a * CliffordAlgebra.ι source9Quadratic z - CliffordAlgebra.ι source9Quadratic z * a) hvalue).symm.trans
      (source9NativeSkewDerivativeRangeEquiv_commutator_vector (source9NativeSkewDerivativeRangeEquiv.symm x) z)

/-- Vector commutator action distinguishes values inside the actual derivative range. -/
theorem source9DerivativeRange_commutator_vector_injective :
    Function.Injective (fun x : source9IdentityChartDerivativeRange => fun z : SpaceIndex → ℝ =>
      (x : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z -
        CliffordAlgebra.ι source9Quadratic z * (x : CliffordAlgebra source9Quadratic)) := by
  intro x y h
  apply source9NativeSkewDerivativeRangeEquiv.symm.injective
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext z
  apply source9CliffordVectorEmbedding_injective
  exact (source9DerivativeRange_commutator_vector x z).symm.trans
    ((congrFun h z).trans (source9DerivativeRange_commutator_vector y z))

private theorem commutator_pair_expansion (a b c : CliffordAlgebra source9Quadratic) :
    (a * b - b * a) * c - c * (a * b - b * a) =
      (a * (b * c - c * b) - (b * c - c * b) * a) -
        (b * (a * c - c * a) - (a * c - c * a) * b) := by
  noncomm_ring

/-- The ambient commutator of two range representatives acts by the exact native matrix bracket. -/
theorem source9NativeSkewDerivativeRange_commutator_pair_vector
    (A B : LieAlgebra.Orthogonal.so SpaceIndex ℝ) (z : SpaceIndex → ℝ) :
    ((source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
        (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
      (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
        (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic)) *
          CliffordAlgebra.ι source9Quadratic z -
      CliffordAlgebra.ι source9Quadratic z *
        ((source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
            (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
          (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
            (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic)) =
      CliffordAlgebra.ι source9Quadratic ((A.val * B.val - B.val * A.val).mulVec z) := by
  rw [commutator_pair_expansion,
    source9NativeSkewDerivativeRangeEquiv_commutator_vector B z,
    source9NativeSkewDerivativeRangeEquiv_commutator_vector A z,
    source9NativeSkewDerivativeRangeEquiv_commutator_vector A (B.val.mulVec z),
    source9NativeSkewDerivativeRangeEquiv_commutator_vector B (A.val.mulVec z)]
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, map_sub]

/-- The precise bracket defect commutes with every original vector; it is not asserted to vanish. -/
theorem source9NativeSkewDerivativeRange_bracket_defect_commutes
    (A B : LieAlgebra.Orthogonal.so SpaceIndex ℝ) (z : SpaceIndex → ℝ) :
    ((source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
        (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
      (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
        (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) -
      (source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆ : CliffordAlgebra source9Quadratic)) *
        CliffordAlgebra.ι source9Quadratic z =
      CliffordAlgebra.ι source9Quadratic z *
        ((source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
            (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
          (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
            (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) -
          (source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆ : CliffordAlgebra source9Quadratic)) := by
  let a : CliffordAlgebra source9Quadratic := source9NativeSkewDerivativeRangeEquiv A
  let b : CliffordAlgebra source9Quadratic := source9NativeSkewDerivativeRangeEquiv B
  let c : CliffordAlgebra source9Quadratic := source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆
  have hpair : (a * b - b * a) * CliffordAlgebra.ι source9Quadratic z -
      CliffordAlgebra.ι source9Quadratic z * (a * b - b * a) =
      CliffordAlgebra.ι source9Quadratic ((A.val * B.val - B.val * A.val).mulVec z) :=
    source9NativeSkewDerivativeRange_commutator_pair_vector A B z
  have hnative : c * CliffordAlgebra.ι source9Quadratic z -
      CliffordAlgebra.ι source9Quadratic z * c =
      CliffordAlgebra.ι source9Quadratic ((A.val * B.val - B.val * A.val).mulVec z) :=
    source9NativeSkewDerivativeRangeEquiv_commutator_vector ⁅A, B⁆ z
  apply sub_eq_zero.mp
  change (a * b - b * a - c) * CliffordAlgebra.ι source9Quadratic z -
    CliffordAlgebra.ι source9Quadratic z * (a * b - b * a - c) = 0
  calc
    _ = ((a * b - b * a) * CliffordAlgebra.ι source9Quadratic z -
        CliffordAlgebra.ι source9Quadratic z * (a * b - b * a)) -
        (c * CliffordAlgebra.ι source9Quadratic z - CliffordAlgebra.ι source9Quadratic z * c) := by
      noncomm_ring
    _ = 0 := sub_eq_zero.mpr (hpair.trans hnative.symm)

/-- Original gamma evaluation of the ambient commutator is BB's canonical native bracket image. -/
theorem source9NativeSkewDerivativeRange_commutator_pair_originalGamma
    (A B : LieAlgebra.Orthogonal.so SpaceIndex ℝ) :
    source9GammaCliffordAlgHom
      ((source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
          (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
        (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
          (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic)) =
      (coordinateToOriginalGammaSkewLieHom ⁅A, B⁆ : GammaMatrix) := by
  have hbracket : (coordinateToOriginalGammaSkewLieHom ⁅A, B⁆ : GammaMatrix) =
      (coordinateToOriginalGammaSkewLieHom A : GammaMatrix) *
          (coordinateToOriginalGammaSkewLieHom B : GammaMatrix) -
        (coordinateToOriginalGammaSkewLieHom B : GammaMatrix) *
          (coordinateToOriginalGammaSkewLieHom A : GammaMatrix) :=
    congrArg (fun M : LieAlgebra.Orthogonal.so SpinIndex ℝ => M.val)
      (coordinateToOriginalGammaSkewLieHom_map_lie A B)
  rw [map_sub, map_mul, map_mul,
    source9NativeSkewDerivativeRangeEquiv_originalGamma A,
    source9NativeSkewDerivativeRangeEquiv_originalGamma B]
  exact hbracket.symm

/-- The same bracket defect has zero original-gamma image, without any gamma-faithfulness premise. -/
theorem source9NativeSkewDerivativeRange_bracket_defect_gamma_zero
    (A B : LieAlgebra.Orthogonal.so SpaceIndex ℝ) :
    source9GammaCliffordAlgHom
      ((source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
          (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
        (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
          (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) -
        (source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆ : CliffordAlgebra source9Quadratic)) = 0 := by
  rw [map_sub, source9NativeSkewDerivativeRange_commutator_pair_originalGamma,
    source9NativeSkewDerivativeRangeEquiv_originalGamma, sub_self]

/-- Ambient commutator closure for this pair is exactly the remaining native bracket equality. -/
theorem source9NativeSkewDerivativeRange_commutator_mem_iff_bracket
    (A B : LieAlgebra.Orthogonal.so SpaceIndex ℝ) :
    ((source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
        (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
      (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
        (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic)) ∈
          source9IdentityChartDerivativeRange ↔
      (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
          (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
        (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
          (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) =
        (source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆ : CliffordAlgebra source9Quadratic) := by
  constructor
  · intro hmem
    let x : source9IdentityChartDerivativeRange :=
      ⟨(source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
          (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
        (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
          (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic), hmem⟩
    have haction : (fun z : SpaceIndex → ℝ =>
        (x : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z -
          CliffordAlgebra.ι source9Quadratic z * (x : CliffordAlgebra source9Quadratic)) =
        (fun z : SpaceIndex → ℝ =>
          (source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆ : CliffordAlgebra source9Quadratic) *
              CliffordAlgebra.ι source9Quadratic z -
            CliffordAlgebra.ι source9Quadratic z *
              (source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆ : CliffordAlgebra source9Quadratic)) := by
      funext z
      exact (source9NativeSkewDerivativeRange_commutator_pair_vector A B z).trans
        (source9NativeSkewDerivativeRangeEquiv_commutator_vector ⁅A, B⁆ z).symm
    exact congrArg (fun y : source9IdentityChartDerivativeRange => (y : CliffordAlgebra source9Quadratic))
      (source9DerivativeRange_commutator_vector_injective haction)
  · intro heq
    exact heq.symm ▸ (source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆).property

#print axioms source9OrderedStrictPlaneVectorVelocity_model
#print axioms source9NativeSkewDerivativeRangeEquiv_commutator_vector
#print axioms source9DerivativeRange_commutator_vector
#print axioms source9DerivativeRange_commutator_vector_injective
#print axioms source9NativeSkewDerivativeRange_commutator_pair_vector
#print axioms source9NativeSkewDerivativeRange_bracket_defect_commutes
#print axioms source9NativeSkewDerivativeRange_commutator_pair_originalGamma
#print axioms source9NativeSkewDerivativeRange_bracket_defect_gamma_zero
#print axioms source9NativeSkewDerivativeRange_commutator_mem_iff_bracket
end
end FCP.BFSSPairedSpin9Clifford
