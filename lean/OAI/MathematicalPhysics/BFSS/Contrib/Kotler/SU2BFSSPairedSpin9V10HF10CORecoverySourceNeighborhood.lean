import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CNLocalOrthogonalRecovery

/-! F10CO: an explicit original-source PBW identity neighborhood satisfying all CN conditions.
Only continuity on the accepted reconstruction domain is used. On this neighborhood,
reconstruction preserves the full actual natural matrix. Equality in the source Spin group,
local kernel control and word-image neighborhood coverage remain separate obligations.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped ContDiff Topology Matrix.Norms.Elementwise

local instance f10coLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) := source9PBWNormedAddCommGroup
local instance f10coLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) := source9PBWNormedSpace

/-- Every original natural matrix entry is the accepted continuous ambient vector action. -/
theorem source9NaturalMatrix_continuous_pbw :
    Continuous (fun g : spinGroup source9Quadratic =>
      ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hpair : Continuous (fun g : spinGroup source9Quadratic =>
      ((g : CliffordAlgebra source9Quadratic), source9CoordinateVector j)) :=
    continuous_subtype_val.prodMk continuous_const
  have h := (continuous_apply i).comp
    ((source9AmbientVectorConjugation_contDiff_pbw (0 : ℕ∞ω)).continuous.comp hpair)
  change Continuous (fun g : spinGroup source9Quadratic =>
    source9AmbientVectorConjugation (g : CliffordAlgebra source9Quadratic)
      (source9CoordinateVector j) i) at h
  have heq : (fun g : spinGroup source9Quadratic =>
      ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) i j) =
    (fun g : spinGroup source9Quadratic =>
      source9AmbientVectorConjugation (g : CliffordAlgebra source9Quadratic)
        (source9CoordinateVector j) i) := by
    funext g
    exact (source9NaturalMatrix_entry_eq_vectorConjugation g i j).trans
      (congrFun (source9AmbientVectorConjugation_eq_spin g (source9CoordinateVector j)).symm i)
  rw [← heq] at h
  exact h

theorem source9SpinCoordinateReconstruction_one :
    source9SpinCoordinateReconstruction (1 : spinGroup source9Quadratic) = 1 := by
  have hc : source9SpinUpperCoordinates (1 : spinGroup source9Quadratic) = 0 := by
    have h : source9SpinUpperCoordinates (source9OrderedStrictPlaneWord (0 : Fin 36 → ℝ)) = 0 :=
      source9OrderedUpperCoordinateMap_zero
    rw [source9OrderedStrictPlaneWord_zero] at h
    exact h
  change source9OrderedStrictPlaneWord
    (source9OrderedUpperCoordinateLocalHomeomorph.symm
      (source9SpinUpperCoordinates (1 : spinGroup source9Quadratic))) = 1
  rw [hc, source9OrderedUpperCoordinateLocalHomeomorph_symm_zero, source9OrderedStrictPlaneWord_zero]

/-- Original-source inputs where reconstruction and both full-matrix recovery conditions hold. -/
noncomputable def source9SpinNaturalMatrixRecoveryNeighborhood : Set (spinGroup source9Quadratic) :=
  (source9SpinCoordinateReconstructionDomain ∩
    (fun g : spinGroup source9Quadratic =>
      ((source9SpinVectorOrthogonalHom (source9SpinCoordinateReconstruction g)) :
        Matrix SpaceIndex SpaceIndex ℝ)) ⁻¹' source9OrthogonalRecoveryNeighborhood) ∩
    (fun g : spinGroup source9Quadratic =>
      ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ)) ⁻¹'
        source9OrthogonalRecoveryNeighborhood

theorem source9SpinNaturalMatrixRecoveryNeighborhood_isOpen_pbw :
    IsOpen source9SpinNaturalMatrixRecoveryNeighborhood := by
  have hrec : ContinuousOn (fun g : spinGroup source9Quadratic =>
      ((source9SpinVectorOrthogonalHom (source9SpinCoordinateReconstruction g)) :
        Matrix SpaceIndex SpaceIndex ℝ)) source9SpinCoordinateReconstructionDomain :=
    source9NaturalMatrix_continuous_pbw.comp_continuousOn'
      source9SpinCoordinateReconstruction_continuousOn_pbw
  have hfirst := hrec.isOpen_inter_preimage source9SpinCoordinateReconstructionDomain_isOpen_pbw
    source9OrthogonalRecoveryNeighborhood_isOpen
  have horiginal := IsOpen.preimage source9NaturalMatrix_continuous_pbw
    source9OrthogonalRecoveryNeighborhood_isOpen
  exact hfirst.inter horiginal

theorem source9SpinNaturalMatrixRecoveryNeighborhood_one_mem :
    (1 : spinGroup source9Quadratic) ∈ source9SpinNaturalMatrixRecoveryNeighborhood := by
  have hm : ((source9SpinVectorOrthogonalHom (1 : spinGroup source9Quadratic)) :
      Matrix SpaceIndex SpaceIndex ℝ) = 1 := by
    change source9SpinVectorMatrixHom (1 : spinGroup source9Quadratic) = 1
    exact map_one source9SpinVectorMatrixHom
  have horiginal : ((source9SpinVectorOrthogonalHom (1 : spinGroup source9Quadratic)) :
      Matrix SpaceIndex SpaceIndex ℝ) ∈ source9OrthogonalRecoveryNeighborhood := by
    rw [hm]
    exact source9OrthogonalRecoveryNeighborhood_one_mem
  have hrec : ((source9SpinVectorOrthogonalHom
      (source9SpinCoordinateReconstruction (1 : spinGroup source9Quadratic))) :
        Matrix SpaceIndex SpaceIndex ℝ) ∈ source9OrthogonalRecoveryNeighborhood := by
    rw [source9SpinCoordinateReconstruction_one]
    exact horiginal
  exact ⟨⟨source9SpinCoordinateReconstructionDomain_one_mem, hrec⟩, horiginal⟩

theorem source9SpinNaturalMatrixRecoveryNeighborhood_mem_nhds_one_pbw :
    source9SpinNaturalMatrixRecoveryNeighborhood ∈ 𝓝 (1 : spinGroup source9Quadratic) :=
  source9SpinNaturalMatrixRecoveryNeighborhood_isOpen_pbw.mem_nhds
    source9SpinNaturalMatrixRecoveryNeighborhood_one_mem

theorem source9SpinNaturalMatrixRecoveryNeighborhood_conditions
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinNaturalMatrixRecoveryNeighborhood) :
    g ∈ source9SpinCoordinateReconstructionDomain ∧
      ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) ∈
        source9OrthogonalRecoveryNeighborhood ∧
      ((source9SpinVectorOrthogonalHom (source9SpinCoordinateReconstruction g)) :
        Matrix SpaceIndex SpaceIndex ℝ) ∈ source9OrthogonalRecoveryNeighborhood :=
  ⟨hg.1.1, hg.2, hg.1.2⟩

/-- Full actual natural-matrix recovery holds throughout this original-source neighborhood. -/
theorem source9NaturalMatrix_reconstruction_eq_on_sourceNeighborhood
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinNaturalMatrixRecoveryNeighborhood) :
    ((source9SpinVectorOrthogonalHom (source9SpinCoordinateReconstruction g)) :
      Matrix SpaceIndex SpaceIndex ℝ) =
      ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) := by
  have hc := source9SpinNaturalMatrixRecoveryNeighborhood_conditions g hg
  exact source9NaturalMatrix_reconstruction_eq_near_one g hc.1 hc.2.2 hc.2.1

#print axioms source9NaturalMatrix_continuous_pbw
#print axioms source9SpinCoordinateReconstruction_one
#print axioms source9SpinNaturalMatrixRecoveryNeighborhood
#print axioms source9SpinNaturalMatrixRecoveryNeighborhood_isOpen_pbw
#print axioms source9SpinNaturalMatrixRecoveryNeighborhood_one_mem
#print axioms source9SpinNaturalMatrixRecoveryNeighborhood_mem_nhds_one_pbw
#print axioms source9SpinNaturalMatrixRecoveryNeighborhood_conditions
#print axioms source9NaturalMatrix_reconstruction_eq_on_sourceNeighborhood
end
end FCP.BFSSPairedSpin9Clifford
