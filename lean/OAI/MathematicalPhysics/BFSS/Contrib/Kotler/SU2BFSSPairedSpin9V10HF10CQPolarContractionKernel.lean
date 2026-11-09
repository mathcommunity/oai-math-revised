import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CPNaturalActionKernelCommutant
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-! F10CQ: source-nine graded commutators and actual kernel contraction criteria.
Adapt K1C's algebraic induction method to the original source, retain grade involution
on arbitrary Clifford elements, and use actual Spin evenness for the ordinary commutator.
The reconstruction-relative element is killed by every literal coordinate contraction.
Scalar classification, two-sign fibers and source equality remain separate obligations.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum

/-- Exact graded commutator for every element of the original source Clifford algebra. -/
theorem source9Clifford_gradedCommutator_eq_polarContraction
    (v : SpaceIndex → ℝ) (x : CliffordAlgebra source9Quadratic) :
    CliffordAlgebra.ι source9Quadratic v * x -
      CliffordAlgebra.involute x * CliffordAlgebra.ι source9Quadratic v =
      CliffordAlgebra.contractLeft (source9Quadratic.polarBilin v) x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      have hr : CliffordAlgebra.involute
          (algebraMap ℝ (CliffordAlgebra source9Quadratic) r) =
          algebraMap ℝ (CliffordAlgebra source9Quadratic) r :=
        (CliffordAlgebra.involute : CliffordAlgebra source9Quadratic →ₐ[ℝ]
          CliffordAlgebra source9Quadratic).commutes r
      rw [hr, CliffordAlgebra.contractLeft_algebraMap]
      rw [Algebra.commutes r (CliffordAlgebra.ι source9Quadratic v)]
      exact sub_self _
  | add x y hx hy =>
      simp only [mul_add, map_add, add_mul]
      rw [← hx, ← hy]
      abel
  | ι_mul u w hu =>
      rw [map_mul, CliffordAlgebra.involute_ι, CliffordAlgebra.contractLeft_ι_mul]
      rw [← mul_assoc (CliffordAlgebra.ι source9Quadratic v)
        (CliffordAlgebra.ι source9Quadratic w) u, CliffordAlgebra.ι_mul_ι_comm v w]
      rw [← hu]
      simp only [neg_mul, sub_mul, mul_sub, Algebra.smul_def,
        QuadraticMap.polarBilin_apply_apply]
      noncomm_ring

/-- Ordinary commutation is the graded formula only under the stated actual evenness hypothesis. -/
theorem source9Clifford_evenCommutator_eq_polarContraction
    (v : SpaceIndex → ℝ) (x : CliffordAlgebra source9Quadratic)
    (hx : x ∈ CliffordAlgebra.even source9Quadratic) :
    CliffordAlgebra.ι source9Quadratic v * x - x * CliffordAlgebra.ι source9Quadratic v =
      CliffordAlgebra.contractLeft (source9Quadratic.polarBilin v) x := by
  simpa only [CliffordAlgebra.involute_eq_of_mem_even hx]
    using source9Clifford_gradedCommutator_eq_polarContraction v x

theorem source9NaturalMatrix_eq_one_iff_polarContractions_zero (g : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) = 1 ↔
      ∀ v : SpaceIndex → ℝ,
        CliffordAlgebra.contractLeft (source9Quadratic.polarBilin v)
          (g : CliffordAlgebra source9Quadratic) = 0 := by
  constructor
  · intro hk
    have hc := (source9NaturalMatrix_eq_one_iff_generator_commutes g).1 hk
    intro v
    have heven : (g : CliffordAlgebra source9Quadratic) ∈ CliffordAlgebra.even source9Quadratic :=
      spinGroup.mem_even g.property
    have h := source9Clifford_evenCommutator_eq_polarContraction v
      (g : CliffordAlgebra source9Quadratic) heven
    rw [(hc v).symm, sub_self] at h
    exact h.symm
  · intro hz
    apply (source9NaturalMatrix_eq_one_iff_generator_commutes g).2
    intro v
    have heven : (g : CliffordAlgebra source9Quadratic) ∈ CliffordAlgebra.even source9Quadratic :=
      spinGroup.mem_even g.property
    have h := source9Clifford_evenCommutator_eq_polarContraction v
      (g : CliffordAlgebra source9Quadratic) heven
    have hzero : CliffordAlgebra.ι source9Quadratic v * (g : CliffordAlgebra source9Quadratic) -
        (g : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic v = 0 :=
      h.trans (hz v)
    exact (sub_eq_zero.mp hzero).symm

/-- Preserve the actual source polarization factor: a half-coordinate gives the literal dual. -/
theorem source9Polar_halfCoordinate_eq_coordinateDual (j : SpaceIndex) :
    source9Quadratic.polarBilin ((1 / 2 : ℝ) • source9CoordinateVector j) =
      (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) := by
  apply LinearMap.ext
  intro v
  have hscale := congrArg (fun d : Module.Dual ℝ (SpaceIndex → ℝ) => d v)
    (map_smul source9Quadratic.polarBilin (1 / 2 : ℝ) (source9CoordinateVector j))
  change source9Quadratic.polarBilin ((1 / 2 : ℝ) • source9CoordinateVector j) v =
    (1 / 2 : ℝ) * source9Quadratic.polarBilin (source9CoordinateVector j) v at hscale
  have hcoord : source9Quadratic.polarBilin (source9CoordinateVector j) v = 2 * v j :=
    source9Quadratic_polar_coordinate j v
  change source9Quadratic.polarBilin ((1 / 2 : ℝ) • source9CoordinateVector j) v = v j
  rw [hscale, hcoord]
  ring

theorem source9NaturalKernel_coordinateContractions_zero
    (g : spinGroup source9Quadratic)
    (hg : ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) = 1) :
    ∀ j : SpaceIndex,
      CliffordAlgebra.contractLeft (Q := source9Quadratic)
        (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) (g : CliffordAlgebra source9Quadratic) = 0 := by
  intro j
  rw [← source9Polar_halfCoordinate_eq_coordinateDual j]
  exact (source9NaturalMatrix_eq_one_iff_polarContractions_zero g).1 hg
    ((1 / 2 : ℝ) • source9CoordinateVector j)

theorem source9NaturalMatrix_eq_iff_relative_polarContractions_zero
    (g h : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) =
      ((source9SpinVectorOrthogonalHom h) : Matrix SpaceIndex SpaceIndex ℝ) ↔
      ∀ v : SpaceIndex → ℝ,
        CliffordAlgebra.contractLeft (source9Quadratic.polarBilin v)
          ((g * h⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) = 0 :=
  (source9NaturalMatrix_eq_iff_relative_kernel g h).trans
    (source9NaturalMatrix_eq_one_iff_polarContractions_zero (g * h⁻¹))

theorem source9Reconstruction_relative_polarContractions_zero_on_sourceNeighborhood
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinNaturalMatrixRecoveryNeighborhood) :
    ∀ v : SpaceIndex → ℝ,
      CliffordAlgebra.contractLeft (source9Quadratic.polarBilin v)
        ((source9SpinCoordinateReconstruction g * g⁻¹ : spinGroup source9Quadratic) :
          CliffordAlgebra source9Quadratic) = 0 :=
  (source9NaturalMatrix_eq_one_iff_polarContractions_zero
    (source9SpinCoordinateReconstruction g * g⁻¹)).1
      (source9Reconstruction_relative_kernel_on_sourceNeighborhood g hg)

theorem source9Reconstruction_relative_coordinateContractions_zero_on_sourceNeighborhood
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinNaturalMatrixRecoveryNeighborhood) :
    ∀ j : SpaceIndex,
      CliffordAlgebra.contractLeft (Q := source9Quadratic)
        (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ))
        ((source9SpinCoordinateReconstruction g * g⁻¹ : spinGroup source9Quadratic) :
          CliffordAlgebra source9Quadratic) = 0 :=
  source9NaturalKernel_coordinateContractions_zero (source9SpinCoordinateReconstruction g * g⁻¹)
    (source9Reconstruction_relative_kernel_on_sourceNeighborhood g hg)

#print axioms source9Clifford_gradedCommutator_eq_polarContraction
#print axioms source9Clifford_evenCommutator_eq_polarContraction
#print axioms source9NaturalMatrix_eq_one_iff_polarContractions_zero
#print axioms source9Polar_halfCoordinate_eq_coordinateDual
#print axioms source9NaturalKernel_coordinateContractions_zero
#print axioms source9NaturalMatrix_eq_iff_relative_polarContractions_zero
#print axioms source9Reconstruction_relative_polarContractions_zero_on_sourceNeighborhood
#print axioms source9Reconstruction_relative_coordinateContractions_zero_on_sourceNeighborhood
end
end FCP.BFSSPairedSpin9Clifford
