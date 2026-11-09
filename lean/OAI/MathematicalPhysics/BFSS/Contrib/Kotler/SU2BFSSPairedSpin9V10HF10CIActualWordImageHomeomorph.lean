import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CHInverseRegularityLocalInjectivity
import Mathlib.Topology.Homeomorph.Defs

/-! F10CI: the accepted parameter neighborhood is homeomorphic to its actual source-word image.
Use the inherited PBW topology and recover parameters through actual natural upper coordinates.
No openness or neighborhood coverage of the word image in the source Spin group is asserted.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped ContDiff Matrix.Norms.Elementwise

local instance f10ciLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) := source9PBWNormedAddCommGroup
local instance f10ciLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) := source9PBWNormedSpace

/-- Upper entries of the actual natural matrix for an arbitrary original source Spin element. -/
noncomputable def source9SpinUpperCoordinates (g : spinGroup source9Quadratic) : Fin 36 → ℝ :=
  source9OrderedUpperProjection
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ)

/-- Continuity uses the actual action's ambient extension and the inherited PBW topology. -/
theorem source9SpinUpperCoordinates_continuous_pbw : Continuous source9SpinUpperCoordinates := by
  apply continuous_pi
  intro i
  have hpair : Continuous (fun g : spinGroup source9Quadratic =>
      ((g : CliffordAlgebra source9Quadratic), source9CoordinateVector (source9StrictPlaneColumn i))) :=
    continuous_subtype_val.prodMk continuous_const
  have h := (continuous_apply (source9StrictPlaneRow i)).comp
    ((source9AmbientVectorConjugation_contDiff_pbw (0 : ℕ∞ω)).continuous.comp hpair)
  change Continuous (fun g : spinGroup source9Quadratic =>
    source9AmbientVectorConjugation (g : CliffordAlgebra source9Quadratic)
      (source9CoordinateVector (source9StrictPlaneColumn i)) (source9StrictPlaneRow i)) at h
  have heq : (fun g : spinGroup source9Quadratic => source9SpinUpperCoordinates g i) =
      (fun g : spinGroup source9Quadratic =>
        source9AmbientVectorConjugation (g : CliffordAlgebra source9Quadratic)
          (source9CoordinateVector (source9StrictPlaneColumn i)) (source9StrictPlaneRow i)) := by
    funext g
    calc
      source9SpinUpperCoordinates g i =
          ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ)
            (source9StrictPlaneRow i) (source9StrictPlaneColumn i) :=
        source9OrderedUpperProjection_apply _ i
      _ = source9SpinVectorConjugation g
          (source9CoordinateVector (source9StrictPlaneColumn i)) (source9StrictPlaneRow i) :=
        source9NaturalMatrix_entry_eq_vectorConjugation g _ _
      _ = source9AmbientVectorConjugation (g : CliffordAlgebra source9Quadratic)
          (source9CoordinateVector (source9StrictPlaneColumn i)) (source9StrictPlaneRow i) :=
        congrFun (source9AmbientVectorConjugation_eq_spin g
          (source9CoordinateVector (source9StrictPlaneColumn i))).symm (source9StrictPlaneRow i)
  rw [← heq] at h
  exact h

/-- Continuity into the original source group, with its existing subtype topology. -/
theorem source9OrderedStrictPlaneWord_continuous_pbw :
    Continuous source9OrderedStrictPlaneWord := by
  have h : Continuous (fun t : Fin 36 → ℝ =>
      ((source9OrderedStrictPlaneWord t) : CliffordAlgebra source9Quadratic)) :=
    (source9PlaneSpinWord_coe_contDiff_pbw (0 : ℕ∞ω) source9StrictPlaneRow
      source9StrictPlaneColumn source9StrictPlaneEnumeration_ne (List.finRange 36)).continuous
  exact continuous_induced_rng.2 h

/-- Exactly the word image of CG's accepted source neighborhood. -/
noncomputable def source9OrderedStrictPlaneWordLocalImage : Set (spinGroup source9Quadratic) :=
  source9OrderedStrictPlaneWord '' source9OrderedUpperCoordinateLocalHomeomorph.source

theorem source9OrderedStrictPlaneWord_coordinate_recovery (t : Fin 36 → ℝ)
    (ht : t ∈ source9OrderedUpperCoordinateLocalHomeomorph.source) :
    source9OrderedUpperCoordinateLocalHomeomorph.symm
      (source9SpinUpperCoordinates (source9OrderedStrictPlaneWord t)) = t := by
  have heq : source9SpinUpperCoordinates (source9OrderedStrictPlaneWord t) =
      source9OrderedUpperCoordinateMap t := rfl
  rw [heq]
  exact source9OrderedUpperCoordinateLocalHomeomorph_left_inv t ht

private theorem wordImage_inverse_mem_source {g : spinGroup source9Quadratic}
    (hg : g ∈ source9OrderedStrictPlaneWordLocalImage) :
    source9OrderedUpperCoordinateLocalHomeomorph.symm (source9SpinUpperCoordinates g) ∈
      source9OrderedUpperCoordinateLocalHomeomorph.source := by
  rcases hg with ⟨t, ht, rfl⟩
  rw [source9OrderedStrictPlaneWord_coordinate_recovery t ht]
  exact ht

private theorem wordImage_coordinates_mem_target {g : spinGroup source9Quadratic}
    (hg : g ∈ source9OrderedStrictPlaneWordLocalImage) :
    source9SpinUpperCoordinates g ∈ source9OrderedUpperCoordinateLocalHomeomorph.target := by
  rcases hg with ⟨t, ht, rfl⟩
  change source9OrderedUpperCoordinateMap t ∈ source9OrderedUpperCoordinateLocalHomeomorph.target
  have heq := congrFun source9OrderedUpperCoordinateLocalHomeomorph_coe t
  rw [← heq]
  exact source9OrderedUpperCoordinateLocalHomeomorph.map_source ht

/-- Homeomorphism onto the actual word image, with an explicit coordinate-recovery inverse. -/
noncomputable def source9OrderedStrictPlaneWordImageHomeomorph :
    source9OrderedUpperCoordinateLocalHomeomorph.source ≃ₜ
      source9OrderedStrictPlaneWordLocalImage where
  toFun t := ⟨source9OrderedStrictPlaneWord t.val, ⟨t.val, t.property, rfl⟩⟩
  invFun g := ⟨source9OrderedUpperCoordinateLocalHomeomorph.symm
    (source9SpinUpperCoordinates g.val), wordImage_inverse_mem_source g.property⟩
  left_inv t := by
    apply Subtype.ext
    exact source9OrderedStrictPlaneWord_coordinate_recovery t.val t.property
  right_inv g := by
    apply Subtype.ext
    change source9OrderedStrictPlaneWord
      (source9OrderedUpperCoordinateLocalHomeomorph.symm (source9SpinUpperCoordinates g.val)) = g.val
    rcases g.property with ⟨t, ht, heq⟩
    rw [← heq, source9OrderedStrictPlaneWord_coordinate_recovery t ht]
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact source9OrderedStrictPlaneWord_continuous_pbw.comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    change Continuous (fun g : source9OrderedStrictPlaneWordLocalImage =>
      source9OrderedUpperCoordinateLocalHomeomorph.symm (source9SpinUpperCoordinates g.val))
    apply continuous_iff_continuousAt.2
    intro g
    have hc : Continuous (fun h : source9OrderedStrictPlaneWordLocalImage =>
        source9SpinUpperCoordinates h.val) :=
      source9SpinUpperCoordinates_continuous_pbw.comp continuous_subtype_val
    have hinv : ContinuousAt
        (source9OrderedUpperCoordinateLocalHomeomorph.symm : (Fin 36 → ℝ) → (Fin 36 → ℝ))
        (source9SpinUpperCoordinates g.val) :=
      source9OrderedUpperCoordinateLocalHomeomorph.continuousAt_symm
        (wordImage_coordinates_mem_target g.property)
    have hcoords : ContinuousAt (fun h : source9OrderedStrictPlaneWordLocalImage =>
        source9SpinUpperCoordinates h.val) g := hc.continuousAt
    exact ContinuousAt.comp
      (f := fun h : source9OrderedStrictPlaneWordLocalImage => source9SpinUpperCoordinates h.val)
      (g := (source9OrderedUpperCoordinateLocalHomeomorph.symm :
        (Fin 36 → ℝ) → (Fin 36 → ℝ))) (x := g) hinv hcoords

theorem source9OrderedStrictPlaneWordImageHomeomorph_apply
    (t : source9OrderedUpperCoordinateLocalHomeomorph.source) :
    (source9OrderedStrictPlaneWordImageHomeomorph t : spinGroup source9Quadratic) =
      source9OrderedStrictPlaneWord t.val := rfl

theorem source9OrderedStrictPlaneWordImageHomeomorph_symm_apply
    (g : source9OrderedStrictPlaneWordLocalImage) :
    (source9OrderedStrictPlaneWordImageHomeomorph.symm g : Fin 36 → ℝ) =
      source9OrderedUpperCoordinateLocalHomeomorph.symm (source9SpinUpperCoordinates g.val) := rfl

#print axioms source9SpinUpperCoordinates
#print axioms source9SpinUpperCoordinates_continuous_pbw
#print axioms source9OrderedStrictPlaneWord_continuous_pbw
#print axioms source9OrderedStrictPlaneWordLocalImage
#print axioms source9OrderedStrictPlaneWord_coordinate_recovery
#print axioms source9OrderedStrictPlaneWordImageHomeomorph
#print axioms source9OrderedStrictPlaneWordImageHomeomorph_apply
#print axioms source9OrderedStrictPlaneWordImageHomeomorph_symm_apply
end
end FCP.BFSSPairedSpin9Clifford
