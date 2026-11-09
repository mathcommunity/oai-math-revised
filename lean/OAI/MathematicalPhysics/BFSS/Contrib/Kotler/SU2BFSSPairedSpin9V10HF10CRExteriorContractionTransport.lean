import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10CQPolarContractionKernel

/-! F10CR: native source-nine contraction transport through the actual exterior linear equivalence.
Both contraction carriers and every coordinate dual remain explicit. Transport scalar equalities
without assuming the linear equivalence preserves products. No common-kernel scalar theorem,
two-sign classification or source Spin equality is asserted.
Candidate until complete strict source compilation and independent audit pass. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum

/-- Contraction commutes with the actual source-nine Clifford/exterior linear change of form. -/
theorem source9Clifford_exterior_contractLeft_transport
    (d : Module.Dual ℝ (SpaceIndex → ℝ)) (x : CliffordAlgebra source9Quadratic) :
    (CliffordAlgebra.equivExterior source9Quadratic) (CliffordAlgebra.contractLeft d x) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (SpaceIndex → ℝ))) d
        ((CliffordAlgebra.equivExterior source9Quadratic) x) := by
  simpa only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply]
    using (CliffordAlgebra.changeForm_contractLeft
      (h := CliffordAlgebra.changeForm.associated_neg_proof) d x)

theorem source9Clifford_contractLeft_zero_iff_exterior
    (d : Module.Dual ℝ (SpaceIndex → ℝ)) (x : CliffordAlgebra source9Quadratic) :
    CliffordAlgebra.contractLeft d x = 0 ↔
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (SpaceIndex → ℝ))) d
        ((CliffordAlgebra.equivExterior source9Quadratic) x) = 0 := by
  constructor
  · intro hz
    exact (source9Clifford_exterior_contractLeft_transport d x).symm.trans
      ((congrArg (CliffordAlgebra.equivExterior source9Quadratic) hz).trans
        (map_zero (CliffordAlgebra.equivExterior source9Quadratic)))
  · intro hz
    apply (CliffordAlgebra.equivExterior source9Quadratic).injective
    exact (source9Clifford_exterior_contractLeft_transport d x).trans
      (hz.trans ((map_zero (CliffordAlgebra.equivExterior source9Quadratic)).symm))

theorem source9NaturalMatrix_eq_one_iff_exteriorPolarContractions_zero
    (g : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) = 1 ↔
      ∀ v : SpaceIndex → ℝ,
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (SpaceIndex → ℝ)))
          (source9Quadratic.polarBilin v)
          ((CliffordAlgebra.equivExterior source9Quadratic) (g : CliffordAlgebra source9Quadratic)) = 0 := by
  constructor
  · intro hk v
    exact (source9Clifford_contractLeft_zero_iff_exterior
      (source9Quadratic.polarBilin v) (g : CliffordAlgebra source9Quadratic)).1
        ((source9NaturalMatrix_eq_one_iff_polarContractions_zero g).1 hk v)
  · intro hz
    apply (source9NaturalMatrix_eq_one_iff_polarContractions_zero g).2
    intro v
    exact (source9Clifford_contractLeft_zero_iff_exterior
      (source9Quadratic.polarBilin v) (g : CliffordAlgebra source9Quadratic)).2 (hz v)

theorem source9NaturalKernel_exteriorCoordinateContractions_zero
    (g : spinGroup source9Quadratic)
    (hg : ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) = 1) :
    ∀ j : SpaceIndex,
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (SpaceIndex → ℝ)))
        (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ))
        ((CliffordAlgebra.equivExterior source9Quadratic) (g : CliffordAlgebra source9Quadratic)) = 0 := by
  intro j
  exact (source9Clifford_contractLeft_zero_iff_exterior
    (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ)) (g : CliffordAlgebra source9Quadratic)).1
      (source9NaturalKernel_coordinateContractions_zero g hg j)

theorem source9NaturalMatrix_eq_iff_relative_exteriorPolarContractions_zero
    (g h : spinGroup source9Quadratic) :
    ((source9SpinVectorOrthogonalHom g) : Matrix SpaceIndex SpaceIndex ℝ) =
      ((source9SpinVectorOrthogonalHom h) : Matrix SpaceIndex SpaceIndex ℝ) ↔
      ∀ v : SpaceIndex → ℝ,
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (SpaceIndex → ℝ)))
          (source9Quadratic.polarBilin v)
          ((CliffordAlgebra.equivExterior source9Quadratic)
            ((g * h⁻¹ : spinGroup source9Quadratic) : CliffordAlgebra source9Quadratic)) = 0 :=
  (source9NaturalMatrix_eq_iff_relative_kernel g h).trans
    (source9NaturalMatrix_eq_one_iff_exteriorPolarContractions_zero (g * h⁻¹))

theorem source9Reconstruction_relative_exteriorPolarContractions_zero_on_sourceNeighborhood
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinNaturalMatrixRecoveryNeighborhood) :
    ∀ v : SpaceIndex → ℝ,
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (SpaceIndex → ℝ)))
        (source9Quadratic.polarBilin v)
        ((CliffordAlgebra.equivExterior source9Quadratic)
          ((source9SpinCoordinateReconstruction g * g⁻¹ : spinGroup source9Quadratic) :
            CliffordAlgebra source9Quadratic)) = 0 :=
  (source9NaturalMatrix_eq_one_iff_exteriorPolarContractions_zero
    (source9SpinCoordinateReconstruction g * g⁻¹)).1
      (source9Reconstruction_relative_kernel_on_sourceNeighborhood g hg)

theorem source9Reconstruction_relative_exteriorCoordinateContractions_zero_on_sourceNeighborhood
    (g : spinGroup source9Quadratic) (hg : g ∈ source9SpinNaturalMatrixRecoveryNeighborhood) :
    ∀ j : SpaceIndex,
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (SpaceIndex → ℝ)))
        (LinearMap.proj j : Module.Dual ℝ (SpaceIndex → ℝ))
        ((CliffordAlgebra.equivExterior source9Quadratic)
          ((source9SpinCoordinateReconstruction g * g⁻¹ : spinGroup source9Quadratic) :
            CliffordAlgebra source9Quadratic)) = 0 :=
  source9NaturalKernel_exteriorCoordinateContractions_zero
    (source9SpinCoordinateReconstruction g * g⁻¹)
    (source9Reconstruction_relative_kernel_on_sourceNeighborhood g hg)

/-- A fixed exterior scalar equality transports back to the same original Clifford scalar. -/
theorem source9Clifford_exterior_eq_scalar_iff (x : CliffordAlgebra source9Quadratic) (c : ℝ) :
    (CliffordAlgebra.equivExterior source9Quadratic) x =
      algebraMap ℝ (ExteriorAlgebra ℝ (SpaceIndex → ℝ)) c ↔
      x = algebraMap ℝ (CliffordAlgebra source9Quadratic) c := by
  have hscalar : (CliffordAlgebra.equivExterior source9Quadratic)
      (algebraMap ℝ (CliffordAlgebra source9Quadratic) c) =
      algebraMap ℝ (ExteriorAlgebra ℝ (SpaceIndex → ℝ)) c := by
    simpa only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply]
      using (CliffordAlgebra.changeForm_algebraMap
        (h := CliffordAlgebra.changeForm.associated_neg_proof (Q := source9Quadratic)) c)
  constructor
  · intro hx
    apply (CliffordAlgebra.equivExterior source9Quadratic).injective
    exact hx.trans hscalar.symm
  · intro hx
    exact (congrArg (CliffordAlgebra.equivExterior source9Quadratic) hx).trans hscalar

#print axioms source9Clifford_exterior_contractLeft_transport
#print axioms source9Clifford_contractLeft_zero_iff_exterior
#print axioms source9NaturalMatrix_eq_one_iff_exteriorPolarContractions_zero
#print axioms source9NaturalKernel_exteriorCoordinateContractions_zero
#print axioms source9NaturalMatrix_eq_iff_relative_exteriorPolarContractions_zero
#print axioms source9Reconstruction_relative_exteriorPolarContractions_zero_on_sourceNeighborhood
#print axioms source9Reconstruction_relative_exteriorCoordinateContractions_zero_on_sourceNeighborhood
#print axioms source9Clifford_exterior_eq_scalar_iff
end
end FCP.BFSSPairedSpin9Clifford
