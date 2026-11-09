import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CUNaturalActionTwoSignFibers
import Mathlib.Topology.Separation.Basic

/-! F10CV: exclude the relative negative sign in a smaller original-source PBW identity neighborhood.
Use reconstruction continuity only on its accepted domain and the original inherited source topology.
On this explicit neighborhood reconstruction is the actual source input, so the accepted word image
is a source identity neighborhood. No global source recovery or openness of the entire word image,
charted-space structure, determinant, covering or physical BFSS conclusion is asserted.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped Topology Matrix.Norms.Elementwise

local instance f10cvLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) := source9PBWNormedAddCommGroup
local instance f10cvLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) := source9PBWNormedSpace

/-- Relative element in the actual original source Spin group. -/
noncomputable def source9SpinReconstructionRelative (g : spinGroup source9Quadratic) :
    spinGroup source9Quadratic := source9SpinCoordinateReconstruction g * g⁻¹

theorem source9SpinReconstructionRelative_continuousOn_pbw :
    ContinuousOn source9SpinReconstructionRelative source9SpinCoordinateReconstructionDomain := by
  have hpair : ContinuousOn (fun g : spinGroup source9Quadratic =>
      (source9SpinCoordinateReconstruction g, g⁻¹)) source9SpinCoordinateReconstructionDomain :=
    source9SpinCoordinateReconstruction_continuousOn_pbw.prodMk
      source9Spin_inv_continuous_pbw.continuousOn
  exact source9Spin_mul_continuous_pbw.comp_continuousOn' hpair

theorem source9SpinReconstructionRelative_one :
    source9SpinReconstructionRelative (1 : spinGroup source9Quadratic) = 1 := by
  simp only [source9SpinReconstructionRelative, source9SpinCoordinateReconstruction_one,
    inv_one, mul_one]

/-- CO's original source neighborhood, restricted by the actual relative negative-sign exclusion. -/
noncomputable def source9SpinExactRecoveryNeighborhood : Set (spinGroup source9Quadratic) :=
  source9SpinNaturalMatrixRecoveryNeighborhood ∩
    source9SpinReconstructionRelative ⁻¹' ({source9NegativeCentral}ᶜ : Set (spinGroup source9Quadratic))

theorem source9SpinExactRecoveryNeighborhood_isOpen_pbw :
    IsOpen source9SpinExactRecoveryNeighborhood := by
  have hrel : ContinuousOn source9SpinReconstructionRelative
      source9SpinNaturalMatrixRecoveryNeighborhood :=
    source9SpinReconstructionRelative_continuousOn_pbw.mono
      (fun g hg => (source9SpinNaturalMatrixRecoveryNeighborhood_conditions g hg).1)
  exact hrel.isOpen_inter_preimage source9SpinNaturalMatrixRecoveryNeighborhood_isOpen_pbw
    isOpen_compl_singleton

theorem source9SpinExactRecoveryNeighborhood_one_mem :
    (1 : spinGroup source9Quadratic) ∈ source9SpinExactRecoveryNeighborhood := by
  refine ⟨source9SpinNaturalMatrixRecoveryNeighborhood_one_mem, ?_⟩
  change source9SpinReconstructionRelative (1 : spinGroup source9Quadratic) ≠ source9NegativeCentral
  rw [source9SpinReconstructionRelative_one]
  exact Ne.symm source9NegativeCentral_ne_one

theorem source9SpinExactRecoveryNeighborhood_mem_nhds_one_pbw :
    source9SpinExactRecoveryNeighborhood ∈ 𝓝 (1 : spinGroup source9Quadratic) :=
  source9SpinExactRecoveryNeighborhood_isOpen_pbw.mem_nhds
    source9SpinExactRecoveryNeighborhood_one_mem

theorem source9SpinExactRecoveryNeighborhood_conditions
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinExactRecoveryNeighborhood) :
    g ∈ source9SpinNaturalMatrixRecoveryNeighborhood ∧
      source9SpinReconstructionRelative g ≠ source9NegativeCentral := hg

/-- The accepted exact two-sign kernel collapses to its identity branch on this smaller set. -/
theorem source9SpinReconstructionRelative_eq_one_on_exactNeighborhood
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinExactRecoveryNeighborhood) :
    source9SpinReconstructionRelative g = 1 := by
  have hc := source9SpinExactRecoveryNeighborhood_conditions g hg
  have hk : ((source9SpinVectorOrthogonalHom (source9SpinReconstructionRelative g)) :
      Matrix SpaceIndex SpaceIndex ℝ) = 1 :=
    source9Reconstruction_relative_kernel_on_sourceNeighborhood g hc.1
  exact ((source9NaturalMatrix_eq_one_iff_two_signs (source9SpinReconstructionRelative g)).1 hk).resolve_right hc.2

/-- Equality is in the actual original source Spin group, not merely in its natural matrix image. -/
theorem source9SpinCoordinateReconstruction_eq_self_on_exactNeighborhood
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinExactRecoveryNeighborhood) :
    source9SpinCoordinateReconstruction g = g := by
  have h := congrArg (fun k : spinGroup source9Quadratic => k * g)
    (source9SpinReconstructionRelative_eq_one_on_exactNeighborhood g hg)
  change (source9SpinCoordinateReconstruction g * g⁻¹) * g = (1 : spinGroup source9Quadratic) * g at h
  simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using h

theorem source9SpinExactRecoveryNeighborhood_subset_wordImage :
    source9SpinExactRecoveryNeighborhood ⊆ source9OrderedStrictPlaneWordLocalImage := by
  intro g hg
  have hc := source9SpinExactRecoveryNeighborhood_conditions g hg
  exact (source9SpinCoordinateReconstruction_eq_self_iff g
    (source9SpinNaturalMatrixRecoveryNeighborhood_conditions g hc.1).1).1
      (source9SpinCoordinateReconstruction_eq_self_on_exactNeighborhood g hg)

/-- The existing actual word image contains an open neighborhood of the original source identity. -/
theorem source9OrderedStrictPlaneWordLocalImage_mem_nhds_one_pbw :
    source9OrderedStrictPlaneWordLocalImage ∈ 𝓝 (1 : spinGroup source9Quadratic) :=
  Filter.mem_of_superset source9SpinExactRecoveryNeighborhood_mem_nhds_one_pbw
    source9SpinExactRecoveryNeighborhood_subset_wordImage

#print axioms source9SpinReconstructionRelative
#print axioms source9SpinReconstructionRelative_continuousOn_pbw
#print axioms source9SpinReconstructionRelative_one
#print axioms source9SpinExactRecoveryNeighborhood
#print axioms source9SpinExactRecoveryNeighborhood_isOpen_pbw
#print axioms source9SpinExactRecoveryNeighborhood_one_mem
#print axioms source9SpinExactRecoveryNeighborhood_mem_nhds_one_pbw
#print axioms source9SpinExactRecoveryNeighborhood_conditions
#print axioms source9SpinReconstructionRelative_eq_one_on_exactNeighborhood
#print axioms source9SpinCoordinateReconstruction_eq_self_on_exactNeighborhood
#print axioms source9SpinExactRecoveryNeighborhood_subset_wordImage
#print axioms source9OrderedStrictPlaneWordLocalImage_mem_nhds_one_pbw
end
end FCP.BFSSPairedSpin9Clifford
