import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10DCDerivativeRangeLiePackaging

/-! F10DD: literal original-gamma evaluation on the actual derivative-range Lie subalgebra.
Use the accepted original Clifford algebra map, CZ's actual range image and DC's canonical
native Lie equivalence. Compare bundled LieHom compositions with the existing BB map.
No source manifold tangent/differential, integration, covering or physical result is asserted.
Candidate until complete strict compilation and independent type/axiom audit. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open FCP.BFSSGamma9

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The original gamma evaluation of every value of the exact canonical range lies in native so(16). -/
theorem source9DerivativeLieSubalgebra_gamma_mem_so
    (x : source9IdentityChartDerivativeLieSubalgebra) :
    source9GammaCliffordAlgHom (x : CliffordAlgebra source9Quadratic) ∈
      LieAlgebra.Orthogonal.so SpinIndex ℝ := by
  let y : source9IdentityChartDerivativeRange := ⟨(x : CliffordAlgebra source9Quadratic), x.property⟩
  have h : source9GammaCliffordAlgHom (x : CliffordAlgebra source9Quadratic) =
      (coordinateToOriginalGammaSkewLieHom (source9NativeSkewDerivativeRangeEquiv.symm y) : GammaMatrix) :=
    source9DerivativeRange_originalGamma y
  exact h.symm ▸ (coordinateToOriginalGammaSkewLieHom
    (source9NativeSkewDerivativeRangeEquiv.symm y)).property

/-- The actual original Clifford gamma map restricted to the actual range, with native skew target. -/
noncomputable def source9DerivativeRangeGammaSkewLieHom :
    source9IdentityChartDerivativeLieSubalgebra →ₗ⁅ℝ⁆ LieAlgebra.Orthogonal.so SpinIndex ℝ where
  toFun := fun x =>
    ⟨source9GammaCliffordAlgHom (x : CliffordAlgebra source9Quadratic),
      source9DerivativeLieSubalgebra_gamma_mem_so x⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    exact map_add source9GammaCliffordAlgHom
      (x : CliffordAlgebra source9Quadratic) (y : CliffordAlgebra source9Quadratic)
  map_smul' := by
    intro c x
    apply Subtype.ext
    exact map_smul source9GammaCliffordAlgHom c (x : CliffordAlgebra source9Quadratic)
  map_lie' := by
    intro x y
    apply Subtype.ext
    have h : source9GammaCliffordAlgHom
        ((x : CliffordAlgebra source9Quadratic) * (y : CliffordAlgebra source9Quadratic) -
          (y : CliffordAlgebra source9Quadratic) * (x : CliffordAlgebra source9Quadratic)) =
      source9GammaCliffordAlgHom (x : CliffordAlgebra source9Quadratic) *
          source9GammaCliffordAlgHom (y : CliffordAlgebra source9Quadratic) -
        source9GammaCliffordAlgHom (y : CliffordAlgebra source9Quadratic) *
          source9GammaCliffordAlgHom (x : CliffordAlgebra source9Quadratic) := by
      rw [map_sub, map_mul, map_mul]
    exact h

theorem source9DerivativeRangeGammaSkewLieHom_apply
    (x : source9IdentityChartDerivativeLieSubalgebra) :
    (source9DerivativeRangeGammaSkewLieHom x : GammaMatrix) =
      source9GammaCliffordAlgHom (x : CliffordAlgebra source9Quadratic) := rfl

/-- Evaluation on the unchanged native representative is exactly BB in the canonical skew target. -/
theorem source9DerivativeRangeGammaSkewLieHom_native_apply
    (A : LieAlgebra.Orthogonal.so SpaceIndex ℝ) :
    source9DerivativeRangeGammaSkewLieHom (source9NativeSkewDerivativeRangeLieEquiv A) =
      coordinateToOriginalGammaSkewLieHom A := by
  apply Subtype.ext
  exact source9NativeSkewDerivativeRangeEquiv_originalGamma A

/-- Full bundled LieHom equality, with the actual original gamma restriction as the left factor. -/
theorem source9DerivativeRangeGammaSkewLieHom_comp_native :
    source9DerivativeRangeGammaSkewLieHom.comp source9NativeSkewDerivativeRangeLieEquiv.toLieHom =
      coordinateToOriginalGammaSkewLieHom := by
  apply LieHom.ext
  intro A
  exact source9DerivativeRangeGammaSkewLieHom_native_apply A

/-- Conversely, BB composed with the actual inverse native Lie equivalence is literal gamma evaluation. -/
theorem source9DerivativeRangeGammaSkewLieHom_factor :
    source9DerivativeRangeGammaSkewLieHom =
      coordinateToOriginalGammaSkewLieHom.comp source9NativeSkewDerivativeRangeLieEquiv.symm.toLieHom := by
  apply LieHom.ext
  intro x
  have h := source9DerivativeRangeGammaSkewLieHom_native_apply
    (source9NativeSkewDerivativeRangeLieEquiv.symm x)
  have heq : source9NativeSkewDerivativeRangeLieEquiv
      (source9NativeSkewDerivativeRangeLieEquiv.symm x) = x :=
    source9NativeSkewDerivativeRangeLieEquiv.apply_symm_apply x
  exact (congrArg source9DerivativeRangeGammaSkewLieHom heq).symm.trans h

#print axioms source9DerivativeLieSubalgebra_gamma_mem_so
#print axioms source9DerivativeRangeGammaSkewLieHom
#print axioms source9DerivativeRangeGammaSkewLieHom_apply
#print axioms source9DerivativeRangeGammaSkewLieHom_native_apply
#print axioms source9DerivativeRangeGammaSkewLieHom_comp_native
#print axioms source9DerivativeRangeGammaSkewLieHom_factor
end
end FCP.BFSSPairedSpin9Clifford
