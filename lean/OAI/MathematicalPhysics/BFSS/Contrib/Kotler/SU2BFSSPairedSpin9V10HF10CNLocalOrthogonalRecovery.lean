import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CMCompletionLocalInverse

/-! F10CN: full orthogonal-matrix recovery from the original strict upper coordinates.
Both matrices must lie in the explicit open identity neighborhood. The final application
recovers the actual natural matrix of the original source element, with both memberships
retained. Source Spin equality and source neighborhood coverage remain open.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped Matrix.Norms.Elementwise

/-- Translate the accepted injective perturbation neighborhood to the identity matrix. -/
noncomputable def source9OrthogonalRecoveryNeighborhood : Set (Matrix SpaceIndex SpaceIndex ℝ) :=
  (fun A : Matrix SpaceIndex SpaceIndex ℝ => A - 1) ⁻¹'
    source9OrthogonalCompletionLocalHomeomorph.source

theorem source9OrthogonalRecoveryNeighborhood_isOpen :
    IsOpen source9OrthogonalRecoveryNeighborhood := by
  have hshift : Continuous (fun A : Matrix SpaceIndex SpaceIndex ℝ => A - 1) :=
    continuous_id.sub continuous_const
  exact IsOpen.preimage hshift source9OrthogonalCompletionLocalHomeomorph.open_source

theorem source9OrthogonalRecoveryNeighborhood_one_mem :
    (1 : Matrix SpaceIndex SpaceIndex ℝ) ∈ source9OrthogonalRecoveryNeighborhood := by
  change (1 : Matrix SpaceIndex SpaceIndex ℝ) - 1 ∈
    source9OrthogonalCompletionLocalHomeomorph.source
  rw [sub_self]
  exact source9OrthogonalCompletionLocalHomeomorph_zero_mem_source

/-- Upper coordinates determine the full orthogonal matrix within the chosen neighborhood. -/
theorem source9Orthogonal_eq_of_upperProjection_eq_near_one
    (A B : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A ∈ Matrix.orthogonalGroup SpaceIndex ℝ)
    (hB : B ∈ Matrix.orthogonalGroup SpaceIndex ℝ)
    (hAn : A ∈ source9OrthogonalRecoveryNeighborhood)
    (hBn : B ∈ source9OrthogonalRecoveryNeighborhood)
    (h : source9OrderedUpperProjection A = source9OrderedUpperProjection B) : A = B := by
  have hd : A - 1 = B - 1 := source9OrthogonalCompletionMap_injOn_source hAn hBn
    (source9OrthogonalCompletionMap_eq_of_upperProjection_eq A B hA hB h)
  exact (sub_add_cancel A 1).symm.trans
    ((congrArg (fun X : Matrix SpaceIndex SpaceIndex ℝ => X + 1) hd).trans (sub_add_cancel B 1))

theorem source9OrderedUpperProjection_injOn_orthogonal_near_one :
    Set.InjOn source9OrderedUpperProjection
      ((Matrix.orthogonalGroup SpaceIndex ℝ : Set (Matrix SpaceIndex SpaceIndex ℝ)) ∩
        source9OrthogonalRecoveryNeighborhood) := by
  intro A hA B hB h
  exact source9Orthogonal_eq_of_upperProjection_eq_near_one A B hA.1 hB.1 hA.2 hB.2 h

theorem source9Orthogonal_eq_of_strict_entries_eq_near_one
    (A B : Matrix SpaceIndex SpaceIndex ℝ)
    (hA : A ∈ Matrix.orthogonalGroup SpaceIndex ℝ)
    (hB : B ∈ Matrix.orthogonalGroup SpaceIndex ℝ)
    (hAn : A ∈ source9OrthogonalRecoveryNeighborhood)
    (hBn : B ∈ source9OrthogonalRecoveryNeighborhood)
    (h : ∀ p : source9StrictPlaneIndex, A p.val.1 p.val.2 = B p.val.1 p.val.2) : A = B :=
  source9Orthogonal_eq_of_upperProjection_eq_near_one A B hA hB hAn hBn
    ((source9OrderedUpperProjection_eq_iff_strict_entries A B).2 h)

/-- This conclusion concerns the actual natural matrices, not equality in the source group. -/
theorem source9NaturalMatrices_eq_of_upperCoordinates_eq_near_one
    (g h : spinGroup source9Quadratic)
    (hgn : ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) ∈
      source9OrthogonalRecoveryNeighborhood)
    (hhn : ((source9SpinVectorOrthogonalHom h) : Matrix SpaceIndex SpaceIndex ℝ) ∈
      source9OrthogonalRecoveryNeighborhood)
    (hc : source9SpinUpperCoordinates g = source9SpinUpperCoordinates h) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) =
      ((source9SpinVectorOrthogonalHom h) : Matrix SpaceIndex SpaceIndex ℝ) := by
  have hp : source9OrderedUpperProjection
      ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) =
    source9OrderedUpperProjection
      ((source9SpinVectorOrthogonalHom h) : Matrix SpaceIndex SpaceIndex ℝ) := hc
  exact source9Orthogonal_eq_of_upperProjection_eq_near_one _ _
    (source9SpinVectorOrthogonalHom g).property (source9SpinVectorOrthogonalHom h).property hgn hhn hp

theorem source9NaturalMatrix_reconstruction_eq_near_one
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinCoordinateReconstructionDomain)
    (hReconstruction : ((source9SpinVectorOrthogonalHom (source9SpinCoordinateReconstruction g)) :
      Matrix SpaceIndex SpaceIndex ℝ) ∈ source9OrthogonalRecoveryNeighborhood)
    (hOriginal : ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) ∈
      source9OrthogonalRecoveryNeighborhood) :
    ((source9SpinVectorOrthogonalHom (source9SpinCoordinateReconstruction g)) :
      Matrix SpaceIndex SpaceIndex ℝ) =
      ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) :=
  source9NaturalMatrices_eq_of_upperCoordinates_eq_near_one
    (source9SpinCoordinateReconstruction g) g hReconstruction hOriginal
    (source9SpinCoordinateReconstruction_upperCoordinates g hg)

#print axioms source9OrthogonalRecoveryNeighborhood
#print axioms source9OrthogonalRecoveryNeighborhood_isOpen
#print axioms source9OrthogonalRecoveryNeighborhood_one_mem
#print axioms source9Orthogonal_eq_of_upperProjection_eq_near_one
#print axioms source9OrderedUpperProjection_injOn_orthogonal_near_one
#print axioms source9Orthogonal_eq_of_strict_entries_eq_near_one
#print axioms source9NaturalMatrices_eq_of_upperCoordinates_eq_near_one
#print axioms source9NaturalMatrix_reconstruction_eq_near_one
end
end FCP.BFSSPairedSpin9Clifford
