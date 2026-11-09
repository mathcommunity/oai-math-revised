import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CIActualWordImageHomeomorph

/-! F10CJ: continuous coordinate reconstruction on an open source Spin neighborhood.
Reconstruction preserves actual upper coordinates and fixes exactly the accepted word image
within this domain. Equality to an arbitrary source input and neighborhood coverage remain open.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped Topology Matrix.Norms.Elementwise

local instance f10cjLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) := source9PBWNormedAddCommGroup
local instance f10cjLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) := source9PBWNormedSpace

/-- The open preimage of the accepted coordinate target in the original source Spin group. -/
noncomputable def source9SpinCoordinateReconstructionDomain : Set (spinGroup source9Quadratic) :=
  source9SpinUpperCoordinates ⁻¹' source9OrderedUpperCoordinateLocalHomeomorph.target

theorem source9SpinCoordinateReconstructionDomain_isOpen_pbw :
    IsOpen source9SpinCoordinateReconstructionDomain :=
  IsOpen.preimage source9SpinUpperCoordinates_continuous_pbw
    source9OrderedUpperCoordinateLocalHomeomorph.open_target

theorem source9SpinCoordinateReconstructionDomain_one_mem :
    (1 : spinGroup source9Quadratic) ∈ source9SpinCoordinateReconstructionDomain := by
  change source9SpinUpperCoordinates (1 : spinGroup source9Quadratic) ∈
    source9OrderedUpperCoordinateLocalHomeomorph.target
  have h : source9SpinUpperCoordinates (source9OrderedStrictPlaneWord (0 : Fin 36 → ℝ)) = 0 :=
    source9OrderedUpperCoordinateMap_zero
  rw [source9OrderedStrictPlaneWord_zero] at h
  rw [h]
  exact source9OrderedUpperCoordinateLocalHomeomorph_zero_mem_target

/-- The specified reconstruction is a total function; its laws below require the stated domain. -/
noncomputable def source9SpinCoordinateReconstruction (g : spinGroup source9Quadratic) :
    spinGroup source9Quadratic :=
  source9OrderedStrictPlaneWord
    (source9OrderedUpperCoordinateLocalHomeomorph.symm (source9SpinUpperCoordinates g))

theorem source9SpinCoordinateReconstruction_continuousOn_pbw :
    ContinuousOn source9SpinCoordinateReconstruction source9SpinCoordinateReconstructionDomain := by
  intro g hg
  have hinv : ContinuousAt
      (source9OrderedUpperCoordinateLocalHomeomorph.symm : (Fin 36 → ℝ) → (Fin 36 → ℝ))
      (source9SpinUpperCoordinates g) :=
    source9OrderedUpperCoordinateLocalHomeomorph.continuousAt_symm hg
  have hcoords : ContinuousAt source9SpinUpperCoordinates g :=
    source9SpinUpperCoordinates_continuous_pbw.continuousAt
  have hparam : ContinuousAt (fun h : spinGroup source9Quadratic =>
      source9OrderedUpperCoordinateLocalHomeomorph.symm (source9SpinUpperCoordinates h)) g :=
    ContinuousAt.comp (f := source9SpinUpperCoordinates)
      (g := (source9OrderedUpperCoordinateLocalHomeomorph.symm :
        (Fin 36 → ℝ) → (Fin 36 → ℝ))) (x := g) hinv hcoords
  have hword : ContinuousAt source9OrderedStrictPlaneWord
      (source9OrderedUpperCoordinateLocalHomeomorph.symm (source9SpinUpperCoordinates g)) :=
    source9OrderedStrictPlaneWord_continuous_pbw.continuousAt
  exact (ContinuousAt.comp
    (f := fun h : spinGroup source9Quadratic =>
      source9OrderedUpperCoordinateLocalHomeomorph.symm (source9SpinUpperCoordinates h))
    (g := source9OrderedStrictPlaneWord) (x := g) hword hparam).continuousWithinAt

theorem source9OrderedStrictPlaneWordLocalImage_subset_reconstructionDomain :
    source9OrderedStrictPlaneWordLocalImage ⊆ source9SpinCoordinateReconstructionDomain := by
  intro g hg
  rcases hg with ⟨t, ht, rfl⟩
  change source9OrderedUpperCoordinateMap t ∈ source9OrderedUpperCoordinateLocalHomeomorph.target
  have heq := congrFun source9OrderedUpperCoordinateLocalHomeomorph_coe t
  rw [← heq]
  exact source9OrderedUpperCoordinateLocalHomeomorph.map_source ht

theorem source9SpinCoordinateReconstruction_mem_wordImage (g : spinGroup source9Quadratic)
    (hg : g ∈ source9SpinCoordinateReconstructionDomain) :
    source9SpinCoordinateReconstruction g ∈ source9OrderedStrictPlaneWordLocalImage := by
  refine ⟨source9OrderedUpperCoordinateLocalHomeomorph.symm (source9SpinUpperCoordinates g), ?_, rfl⟩
  exact source9OrderedUpperCoordinateLocalHomeomorph.map_target hg

/-- Coordinate recovery does not assert equality of source Spin elements or of their full matrices. -/
theorem source9SpinCoordinateReconstruction_upperCoordinates (g : spinGroup source9Quadratic)
    (hg : g ∈ source9SpinCoordinateReconstructionDomain) :
    source9SpinUpperCoordinates (source9SpinCoordinateReconstruction g) =
      source9SpinUpperCoordinates g := by
  change source9OrderedUpperCoordinateMap
    (source9OrderedUpperCoordinateLocalHomeomorph.symm (source9SpinUpperCoordinates g)) =
      source9SpinUpperCoordinates g
  exact source9OrderedUpperCoordinateLocalHomeomorph_right_inv (source9SpinUpperCoordinates g) hg

/-- On this domain, the fixed points are exactly the accepted word image; coverage is separate. -/
theorem source9SpinCoordinateReconstruction_eq_self_iff (g : spinGroup source9Quadratic)
    (hg : g ∈ source9SpinCoordinateReconstructionDomain) :
    source9SpinCoordinateReconstruction g = g ↔ g ∈ source9OrderedStrictPlaneWordLocalImage := by
  constructor
  · intro hfix
    rw [← hfix]
    exact source9SpinCoordinateReconstruction_mem_wordImage g hg
  · intro himage
    rcases himage with ⟨t, ht, rfl⟩
    change source9OrderedStrictPlaneWord
      (source9OrderedUpperCoordinateLocalHomeomorph.symm
        (source9SpinUpperCoordinates (source9OrderedStrictPlaneWord t))) =
          source9OrderedStrictPlaneWord t
    rw [source9OrderedStrictPlaneWord_coordinate_recovery t ht]

#print axioms source9SpinCoordinateReconstructionDomain
#print axioms source9SpinCoordinateReconstructionDomain_isOpen_pbw
#print axioms source9SpinCoordinateReconstructionDomain_one_mem
#print axioms source9SpinCoordinateReconstruction
#print axioms source9SpinCoordinateReconstruction_continuousOn_pbw
#print axioms source9OrderedStrictPlaneWordLocalImage_subset_reconstructionDomain
#print axioms source9SpinCoordinateReconstruction_mem_wordImage
#print axioms source9SpinCoordinateReconstruction_upperCoordinates
#print axioms source9SpinCoordinateReconstruction_eq_self_iff
end
end FCP.BFSSPairedSpin9Clifford
