import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CORecoverySourceNeighborhood

/-! F10CP: source-exact kernel and relative-fiber commutation for the actual nine-vector action.
Reuse the earlier K1A cancellation method on the original nine-vector source, and extend
generator commutation by Clifford induction. Apply CO's matrix equality to the actual
relative reconstruction element. No scalar/two-sign classification or source equality is asserted.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum

theorem source9NaturalMatrix_eq_one_iff_trivialAction (g : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) = 1 ↔
      ∀ z : SpaceIndex → ℝ, source9SpinVectorConjugation g z = z := by
  constructor
  · intro hm z
    exact (source9SpinVectorOrthogonalHom_mulVec g z).symm.trans
      ((congrArg (fun A : Matrix SpaceIndex SpaceIndex ℝ => A.mulVec z) hm).trans
        (Matrix.one_mulVec z))
  · intro h
    have hrep : source9SpinVectorRepresentation g =
        (1 : (SpaceIndex → ℝ) →ₗ[ℝ] (SpaceIndex → ℝ)) := by
      apply LinearMap.ext
      intro z
      exact h z
    have hm := congrArg
      (fun L : (SpaceIndex → ℝ) →ₗ[ℝ] (SpaceIndex → ℝ) =>
        (LinearMap.toMatrixAlgEquiv' :
          ((SpaceIndex → ℝ) →ₗ[ℝ] (SpaceIndex → ℝ)) ≃ₐ[ℝ]
            Matrix SpaceIndex SpaceIndex ℝ) L) hrep
    have hmatrix :
        (LinearMap.toMatrixAlgEquiv' :
          ((SpaceIndex → ℝ) →ₗ[ℝ] (SpaceIndex → ℝ)) ≃ₐ[ℝ]
            Matrix SpaceIndex SpaceIndex ℝ) (source9SpinVectorRepresentation g) = 1 := by
      simpa only [map_one] using hm
    have hactual : ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) =
        (LinearMap.toMatrixAlgEquiv' :
          ((SpaceIndex → ℝ) →ₗ[ℝ] (SpaceIndex → ℝ)) ≃ₐ[ℝ]
            Matrix SpaceIndex SpaceIndex ℝ) (source9SpinVectorRepresentation g) := rfl
    exact hactual.trans hmatrix

/-- Actual conjugation is trivial exactly when the source element commutes with every vector. -/
theorem source9Spin_trivialAction_iff_generator_commutes (g : spinGroup source9Quadratic) :
    (∀ z : SpaceIndex → ℝ, source9SpinVectorConjugation g z = z) ↔
      ∀ z : SpaceIndex → ℝ,
        (g : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z =
          CliffordAlgebra.ι source9Quadratic z * (g : CliffordAlgebra source9Quadratic) := by
  have hleft : ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) *
      (g : CliffordAlgebra source9Quadratic) = 1 :=
    congrArg (fun x : spinGroup source9Quadratic => (x : CliffordAlgebra source9Quadratic))
      (inv_mul_cancel g)
  have hright : (g : CliffordAlgebra source9Quadratic) *
      ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) = 1 :=
    congrArg (fun x : spinGroup source9Quadratic => (x : CliffordAlgebra source9Quadratic))
      (mul_inv_cancel g)
  constructor
  · intro h z
    have hc : CliffordAlgebra.ι source9Quadratic z =
        (g : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z *
          ((g⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) :=
      (congrArg (CliffordAlgebra.ι source9Quadratic) (h z)).symm.trans
        (source9SpinVectorConjugation_ι g z)
    have hc' := congrArg
      (fun x : CliffordAlgebra source9Quadratic => x * (g : CliffordAlgebra source9Quadratic)) hc
    simpa only [mul_assoc, hleft, mul_one] using hc'.symm
  · intro h z
    apply source9CliffordVectorEmbedding_injective
    rw [source9SpinVectorConjugation_ι, h z, mul_assoc, hright, mul_one]

theorem source9NaturalMatrix_eq_one_iff_generator_commutes (g : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) = 1 ↔
      ∀ z : SpaceIndex → ℝ,
        (g : CliffordAlgebra source9Quadratic) * CliffordAlgebra.ι source9Quadratic z =
          CliffordAlgebra.ι source9Quadratic z * (g : CliffordAlgebra source9Quadratic) :=
  (source9NaturalMatrix_eq_one_iff_trivialAction g).trans
    (source9Spin_trivialAction_iff_generator_commutes g)

/-- The commutation condition concerns the whole original Clifford algebra, not just coordinates. -/
theorem source9NaturalMatrix_eq_one_iff_clifford_commutes (g : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) = 1 ↔
      ∀ x : CliffordAlgebra source9Quadratic,
        (g : CliffordAlgebra source9Quadratic) * x = x * (g : CliffordAlgebra source9Quadratic) := by
  constructor
  · intro hk
    have hc := (source9NaturalMatrix_eq_one_iff_generator_commutes g).1 hk
    intro x
    induction x using CliffordAlgebra.induction with
    | algebraMap r => exact (Algebra.commutes r (g : CliffordAlgebra source9Quadratic)).symm
    | ι z => exact hc z
    | mul a b ha hb =>
        calc
          (g : CliffordAlgebra source9Quadratic) * (a * b) =
              ((g : CliffordAlgebra source9Quadratic) * a) * b := (mul_assoc _ _ _).symm
          _ = (a * (g : CliffordAlgebra source9Quadratic)) * b :=
            congrArg (fun t : CliffordAlgebra source9Quadratic => t * b) ha
          _ = a * ((g : CliffordAlgebra source9Quadratic) * b) := mul_assoc _ _ _
          _ = a * (b * (g : CliffordAlgebra source9Quadratic)) :=
            congrArg (fun t : CliffordAlgebra source9Quadratic => a * t) hb
          _ = (a * b) * (g : CliffordAlgebra source9Quadratic) := (mul_assoc _ _ _).symm
    | add a b ha hb => rw [mul_add, add_mul, ha, hb]
  · intro h
    exact (source9NaturalMatrix_eq_one_iff_generator_commutes g).2
      (fun z => h (CliffordAlgebra.ι source9Quadratic z))

theorem source9NaturalMatrix_eq_iff_relative_kernel (g h : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) =
      ((source9SpinVectorOrthogonalHom h) : Matrix SpaceIndex SpaceIndex ℝ) ↔
    ((source9SpinVectorOrthogonalHom (g * h⁻¹)) : Matrix SpaceIndex SpaceIndex ℝ) = 1 := by
  constructor
  · intro hm
    have hh : source9SpinVectorOrthogonalHom g = source9SpinVectorOrthogonalHom h :=
      Subtype.ext hm
    have hk : source9SpinVectorOrthogonalHom (g * h⁻¹) = 1 := by
      rw [map_mul, map_inv, hh, mul_inv_cancel]
    exact congrArg (fun A : Matrix.orthogonalGroup SpaceIndex ℝ =>
      (A : Matrix SpaceIndex SpaceIndex ℝ)) hk
  · intro hm
    have hk : source9SpinVectorOrthogonalHom (g * h⁻¹) = 1 := Subtype.ext hm
    have hcancel : g = (g * h⁻¹) * h := by rw [mul_assoc, inv_mul_cancel, mul_one]
    have hh : source9SpinVectorOrthogonalHom g = source9SpinVectorOrthogonalHom h := by
      calc
        source9SpinVectorOrthogonalHom g = source9SpinVectorOrthogonalHom ((g * h⁻¹) * h) :=
          congrArg source9SpinVectorOrthogonalHom hcancel
        _ = source9SpinVectorOrthogonalHom (g * h⁻¹) * source9SpinVectorOrthogonalHom h :=
          map_mul source9SpinVectorOrthogonalHom (g * h⁻¹) h
        _ = source9SpinVectorOrthogonalHom h := by rw [hk, one_mul]
    exact congrArg (fun A : Matrix.orthogonalGroup SpaceIndex ℝ =>
      (A : Matrix SpaceIndex SpaceIndex ℝ)) hh

theorem source9NaturalMatrix_eq_iff_relative_commutes (g h : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) =
      ((source9SpinVectorOrthogonalHom h) : Matrix SpaceIndex SpaceIndex ℝ) ↔
      ∀ x : CliffordAlgebra source9Quadratic,
        ((g * h⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) * x =
          x * ((g * h⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic) :=
  (source9NaturalMatrix_eq_iff_relative_kernel g h).trans
    (source9NaturalMatrix_eq_one_iff_clifford_commutes (g * h⁻¹))

theorem source9Reconstruction_relative_kernel_on_sourceNeighborhood
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinNaturalMatrixRecoveryNeighborhood) :
    ((source9SpinVectorOrthogonalHom (source9SpinCoordinateReconstruction g * g⁻¹)) :
      Matrix SpaceIndex SpaceIndex ℝ) = 1 :=
  (source9NaturalMatrix_eq_iff_relative_kernel (source9SpinCoordinateReconstruction g) g).1
    (source9NaturalMatrix_reconstruction_eq_on_sourceNeighborhood g hg)

theorem source9Reconstruction_relative_commutes_on_sourceNeighborhood
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinNaturalMatrixRecoveryNeighborhood) :
    ∀ x : CliffordAlgebra source9Quadratic,
      ((source9SpinCoordinateReconstruction g * g⁻¹ : spinGroup source9Quadratic) :
        CliffordAlgebra source9Quadratic) * x =
      x * ((source9SpinCoordinateReconstruction g * g⁻¹ : spinGroup source9Quadratic) :
        CliffordAlgebra source9Quadratic) :=
  (source9NaturalMatrix_eq_one_iff_clifford_commutes
    (source9SpinCoordinateReconstruction g * g⁻¹)).1
      (source9Reconstruction_relative_kernel_on_sourceNeighborhood g hg)

#print axioms source9NaturalMatrix_eq_one_iff_trivialAction
#print axioms source9Spin_trivialAction_iff_generator_commutes
#print axioms source9NaturalMatrix_eq_one_iff_generator_commutes
#print axioms source9NaturalMatrix_eq_one_iff_clifford_commutes
#print axioms source9NaturalMatrix_eq_iff_relative_kernel
#print axioms source9NaturalMatrix_eq_iff_relative_commutes
#print axioms source9Reconstruction_relative_kernel_on_sourceNeighborhood
#print axioms source9Reconstruction_relative_commutes_on_sourceNeighborhood
end
end FCP.BFSSPairedSpin9Clifford
