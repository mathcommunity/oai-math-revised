import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CVExactSourceRecoveryNeighborhood
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! F10CW: a specified open identity chart on the original source Spin group.
Restrict the accepted word/coordinate inverse to CV's open exact-recovery source set and the
matching open parameter set. The source, target and both functions are exposed literally.
No atlas, manifold or Lie-group instance, transition regularity, tangent identification,
differential comparison, global source recovery or physical BFSS conclusion is asserted.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped Topology Matrix.Norms.Elementwise

local instance f10cwLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) := source9PBWNormedAddCommGroup
local instance f10cwLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) := source9PBWNormedSpace

/-- The old parameter source restricted to words lying in the explicit exact-recovery source set. -/
noncomputable def source9SpinIdentityChartTarget : Set (Fin 36 → ℝ) :=
  source9OrderedUpperCoordinateLocalHomeomorph.source ∩
    source9OrderedStrictPlaneWord ⁻¹' source9SpinExactRecoveryNeighborhood

theorem source9SpinIdentityChartTarget_isOpen : IsOpen source9SpinIdentityChartTarget :=
  source9OrderedUpperCoordinateLocalHomeomorph.open_source.inter
    (IsOpen.preimage source9OrderedStrictPlaneWord_continuous_pbw
      source9SpinExactRecoveryNeighborhood_isOpen_pbw)

theorem source9SpinIdentityChartTarget_zero_mem :
    (0 : Fin 36 → ℝ) ∈ source9SpinIdentityChartTarget := by
  refine ⟨source9OrderedUpperCoordinateLocalHomeomorph_zero_mem_source, ?_⟩
  change source9OrderedStrictPlaneWord (0 : Fin 36 → ℝ) ∈ source9SpinExactRecoveryNeighborhood
  rw [source9OrderedStrictPlaneWord_zero]
  exact source9SpinExactRecoveryNeighborhood_one_mem

/-- The actual source identity chart, with inverse given by the original ordered Spin word. -/
noncomputable def source9SpinIdentityLocalChart :
    OpenPartialHomeomorph (spinGroup source9Quadratic) (Fin 36 → ℝ) where
  toFun g := source9OrderedUpperCoordinateLocalHomeomorph.symm (source9SpinUpperCoordinates g)
  invFun := source9OrderedStrictPlaneWord
  source := source9SpinExactRecoveryNeighborhood
  target := source9SpinIdentityChartTarget
  map_source' := by
    intro g hg
    refine ⟨?_, ?_⟩
    · exact source9OrderedUpperCoordinateLocalHomeomorph.map_target
        (source9SpinNaturalMatrixRecoveryNeighborhood_conditions g
          (source9SpinExactRecoveryNeighborhood_conditions g hg).1).1
    · change source9SpinCoordinateReconstruction g ∈ source9SpinExactRecoveryNeighborhood
      rw [source9SpinCoordinateReconstruction_eq_self_on_exactNeighborhood g hg]
      exact hg
  map_target' := by
    intro t ht
    exact ht.2
  left_inv' := by
    intro g hg
    change source9SpinCoordinateReconstruction g = g
    exact source9SpinCoordinateReconstruction_eq_self_on_exactNeighborhood g hg
  right_inv' := by
    intro t ht
    exact source9OrderedStrictPlaneWord_coordinate_recovery t ht.1
  continuousOn_toFun :=
    source9OrderedUpperCoordinateLocalHomeomorph.continuousOn_symm.comp'
      source9SpinUpperCoordinates_continuous_pbw.continuousOn
      (fun g hg => (source9SpinNaturalMatrixRecoveryNeighborhood_conditions g
        (source9SpinExactRecoveryNeighborhood_conditions g hg).1).1)
  continuousOn_invFun := source9OrderedStrictPlaneWord_continuous_pbw.continuousOn
  open_source := source9SpinExactRecoveryNeighborhood_isOpen_pbw
  open_target := source9SpinIdentityChartTarget_isOpen

theorem source9SpinIdentityLocalChart_source :
    source9SpinIdentityLocalChart.source = source9SpinExactRecoveryNeighborhood := rfl

theorem source9SpinIdentityLocalChart_target :
    source9SpinIdentityLocalChart.target = source9SpinIdentityChartTarget := rfl

theorem source9SpinIdentityLocalChart_coe :
    (source9SpinIdentityLocalChart : spinGroup source9Quadratic → (Fin 36 → ℝ)) =
      (fun g : spinGroup source9Quadratic =>
        source9OrderedUpperCoordinateLocalHomeomorph.symm (source9SpinUpperCoordinates g)) := rfl

theorem source9SpinIdentityLocalChart_symm_coe :
    (source9SpinIdentityLocalChart.symm : (Fin 36 → ℝ) → spinGroup source9Quadratic) =
      source9OrderedStrictPlaneWord := rfl

theorem source9SpinIdentityLocalChart_one :
    source9SpinIdentityLocalChart (1 : spinGroup source9Quadratic) = 0 := by
  have h := source9OrderedStrictPlaneWord_coordinate_recovery (0 : Fin 36 → ℝ)
    source9OrderedUpperCoordinateLocalHomeomorph_zero_mem_source
  rw [source9OrderedStrictPlaneWord_zero] at h
  exact h

theorem source9SpinIdentityLocalChart_one_mem_source :
    (1 : spinGroup source9Quadratic) ∈ source9SpinIdentityLocalChart.source :=
  source9SpinExactRecoveryNeighborhood_one_mem

theorem source9SpinIdentityLocalChart_zero_mem_target :
    (0 : Fin 36 → ℝ) ∈ source9SpinIdentityLocalChart.target :=
  source9SpinIdentityChartTarget_zero_mem

theorem source9SpinIdentityLocalChart_bijOn :
    Set.BijOn source9SpinIdentityLocalChart source9SpinExactRecoveryNeighborhood
      source9SpinIdentityChartTarget := source9SpinIdentityLocalChart.bijOn

#print axioms source9SpinIdentityChartTarget
#print axioms source9SpinIdentityChartTarget_isOpen
#print axioms source9SpinIdentityChartTarget_zero_mem
#print axioms source9SpinIdentityLocalChart
#print axioms source9SpinIdentityLocalChart_source
#print axioms source9SpinIdentityLocalChart_target
#print axioms source9SpinIdentityLocalChart_coe
#print axioms source9SpinIdentityLocalChart_symm_coe
#print axioms source9SpinIdentityLocalChart_one
#print axioms source9SpinIdentityLocalChart_one_mem_source
#print axioms source9SpinIdentityLocalChart_zero_mem_target
#print axioms source9SpinIdentityLocalChart_bijOn
end
end FCP.BFSSPairedSpin9Clifford
