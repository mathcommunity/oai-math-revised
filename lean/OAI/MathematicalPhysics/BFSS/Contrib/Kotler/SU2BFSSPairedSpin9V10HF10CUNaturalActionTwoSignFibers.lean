import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CTExteriorScalarKernel
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10UActualNegativeCentralSO48ImageProbe
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! F10CU: exact two-sign kernel and equal-action fibers of the original natural nine-vector map.
Use actual source Spin unitarity, real scalar faithfulness and the accepted negative central
source element. The fiber statement asserts no target surjectivity or topological covering.
Reconstruction is equal to the input or its negative source sign on the accepted neighborhood;
excluding that negative branch locally remains a separate obligation.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum

theorem source9Spin_scalar_coefficient_square_one
    (g : spinGroup source9Quadratic) (c : ℝ)
    (hc : (g : CliffordAlgebra source9Quadratic) = algebraMap ℝ (CliffordAlgebra source9Quadratic) c) :
    c * c = 1 := by
  have hstar : star (g : CliffordAlgebra source9Quadratic) = (g : CliffordAlgebra source9Quadratic) := by
    rw [hc, CliffordAlgebra.star_algebraMap]
  have hunit : star (g : CliffordAlgebra source9Quadratic) * (g : CliffordAlgebra source9Quadratic) = 1 :=
    spinGroup.star_mul_self_of_mem g.property
  rw [hstar, hc] at hunit
  have hmap : algebraMap ℝ (CliffordAlgebra source9Quadratic) (c * c) =
      algebraMap ℝ (CliffordAlgebra source9Quadratic) (1 : ℝ) := by
    simpa only [map_mul, map_one] using hunit
  exact (FaithfulSMul.algebraMap_injective ℝ (CliffordAlgebra source9Quadratic)) hmap

theorem source9Spin_scalar_coefficient_two_signs
    (g : spinGroup source9Quadratic) (c : ℝ)
    (hc : (g : CliffordAlgebra source9Quadratic) = algebraMap ℝ (CliffordAlgebra source9Quadratic) c) :
    c = 1 ∨ c = -1 := by
  have hsq := source9Spin_scalar_coefficient_square_one g c hc
  have hfactor : (c - 1) * (c + 1) = 0 := by
    calc
      (c - 1) * (c + 1) = c * c - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · exact Or.inl (sub_eq_zero.mp hminus)
  · have hneg : c = -1 := by linarith
    exact Or.inr hneg

theorem source9NaturalKernel_clifford_one_or_neg_one
    (g : spinGroup source9Quadratic)
    (hg : ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) = 1) :
    (g : CliffordAlgebra source9Quadratic) = 1 ∨ (g : CliffordAlgebra source9Quadratic) = -1 := by
  obtain ⟨c, hc⟩ := (source9NaturalMatrix_eq_one_iff_clifford_scalar g).1 hg
  rcases source9Spin_scalar_coefficient_two_signs g c hc with hpos | hneg
  · left
    simpa only [hpos, map_one] using hc
  · right
    simpa only [hneg, map_neg, map_one] using hc

/-- Both signs are the actual original source group elements, with no new abstract kernel carrier. -/
theorem source9NaturalMatrix_eq_one_iff_two_signs (g : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) = 1 ↔
      g = 1 ∨ g = source9NegativeCentral := by
  constructor
  · intro hk
    rcases source9NaturalKernel_clifford_one_or_neg_one g hk with hpos | hneg
    · left
      apply Subtype.ext
      change (g : CliffordAlgebra source9Quadratic) = (1 : CliffordAlgebra source9Quadratic)
      exact hpos
    · right
      apply Subtype.ext
      change (g : CliffordAlgebra source9Quadratic) = (-1 : CliffordAlgebra source9Quadratic)
      exact hneg
  · rintro (rfl | rfl)
    · change source9SpinVectorMatrixHom (1 : spinGroup source9Quadratic) = 1
      exact map_one source9SpinVectorMatrixHom
    · apply (source9NaturalMatrix_eq_one_iff_clifford_scalar source9NegativeCentral).2
      exact ⟨-1, by simp only [source9NegativeCentral_coe, map_neg, map_one]⟩

theorem source9NegativeCentral_naturalMatrix_one :
    ((source9SpinVectorOrthogonalHom source9NegativeCentral) : Matrix SpaceIndex SpaceIndex ℝ) = 1 :=
  (source9NaturalMatrix_eq_one_iff_two_signs source9NegativeCentral).2 (Or.inr rfl)

/-- Exact fibers over attained natural matrices; no surjectivity or covering assertion is included. -/
theorem source9NaturalMatrix_eq_iff_two_sign_fiber (g h : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) =
      ((source9SpinVectorOrthogonalHom h) : Matrix SpaceIndex SpaceIndex ℝ) ↔
      g = h ∨ g = source9NegativeCentral * h := by
  constructor
  · intro hm
    have hk := (source9NaturalMatrix_eq_iff_relative_kernel g h).1 hm
    rcases (source9NaturalMatrix_eq_one_iff_two_signs (g * h⁻¹)).1 hk with hpos | hneg
    · left
      calc
        g = (g * h⁻¹) * h := by rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = h := by rw [hpos, one_mul]
    · right
      calc
        g = (g * h⁻¹) * h := by rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = source9NegativeCentral * h := by rw [hneg]
  · rintro (hsame | hneg)
    · exact congrArg (fun k : spinGroup source9Quadratic =>
        ((source9SpinVectorOrthogonalHom k) : Matrix SpaceIndex SpaceIndex ℝ)) hsame
    · have hcentral : source9SpinVectorOrthogonalHom source9NegativeCentral = 1 :=
        Subtype.ext source9NegativeCentral_naturalMatrix_one
      have hh : source9SpinVectorOrthogonalHom g = source9SpinVectorOrthogonalHom h := by
        calc
          source9SpinVectorOrthogonalHom g = source9SpinVectorOrthogonalHom (source9NegativeCentral * h) :=
            congrArg source9SpinVectorOrthogonalHom hneg
          _ = source9SpinVectorOrthogonalHom source9NegativeCentral * source9SpinVectorOrthogonalHom h :=
            map_mul source9SpinVectorOrthogonalHom source9NegativeCentral h
          _ = source9SpinVectorOrthogonalHom h := by rw [hcentral, one_mul]
      exact congrArg (fun A : Matrix.orthogonalGroup SpaceIndex ℝ =>
        (A : Matrix SpaceIndex SpaceIndex ℝ)) hh

theorem source9NaturalMatrix_fiber_signs_distinct (g : spinGroup source9Quadratic) :
    g ≠ source9NegativeCentral * g := by
  intro h
  have hprod : (1 : spinGroup source9Quadratic) * g = source9NegativeCentral * g := by
    simpa only [one_mul] using h
  exact source9NegativeCentral_ne_one (mul_right_cancel hprod).symm

theorem source9NaturalMatrix_not_injective :
    ¬ Function.Injective (fun g : spinGroup source9Quadratic =>
      ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ)) := by
  intro hinj
  have hone : ((source9SpinVectorOrthogonalHom (1 : spinGroup source9Quadratic)) :
      Matrix SpaceIndex SpaceIndex ℝ) = 1 := by
    change source9SpinVectorMatrixHom (1 : spinGroup source9Quadratic) = 1
    exact map_one source9SpinVectorMatrixHom
  exact source9NegativeCentral_ne_one
    (hinj (source9NegativeCentral_naturalMatrix_one.trans hone.symm))

theorem source9Reconstruction_eq_self_or_negative_on_sourceNeighborhood
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinNaturalMatrixRecoveryNeighborhood) :
    source9SpinCoordinateReconstruction g = g ∨
      source9SpinCoordinateReconstruction g = source9NegativeCentral * g :=
  (source9NaturalMatrix_eq_iff_two_sign_fiber (source9SpinCoordinateReconstruction g) g).1
    (source9NaturalMatrix_reconstruction_eq_on_sourceNeighborhood g hg)

#print axioms source9Spin_scalar_coefficient_square_one
#print axioms source9Spin_scalar_coefficient_two_signs
#print axioms source9NaturalKernel_clifford_one_or_neg_one
#print axioms source9NaturalMatrix_eq_one_iff_two_signs
#print axioms source9NegativeCentral_naturalMatrix_one
#print axioms source9NaturalMatrix_eq_iff_two_sign_fiber
#print axioms source9NaturalMatrix_fiber_signs_distinct
#print axioms source9NaturalMatrix_not_injective
#print axioms source9Reconstruction_eq_self_or_negative_on_sourceNeighborhood
end
end FCP.BFSSPairedSpin9Clifford
