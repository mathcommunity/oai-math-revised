import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10QSourceSpinOrientationDetOneProbe

/-!
K1D18V10H-F10BC — exact global algebraic source Spin9 to SO(16)
packaging on the original real 16-dimensional gamma carrier.

Accepted V10E gives the genuine whole-source-group homomorphism
into Matrix.orthogonalGroup SpinIndex ℝ. Accepted F10Q proves
that the determinant of every one of those exact gamma images is
+1. This stage packages precisely those two accepted facts as a
MonoidHom into Matrix.specialOrthogonalGroup SpinIndex ℝ.

This is algebraic only. It does not supply a source Lie-group
manifold, continuity, smoothness, a differential computation,
identification with the independently accepted F10BB LieHom,
a topological covering, a Spin(16) lift, Fock implementation,
gauge-domain compatibility, or any BFSS spectral consequence.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- Every exact original gamma image of a genuine source Spin9
element belongs to the pinned special orthogonal group SO(16). -/
theorem source9SpinGammaMatrix_mem_specialOrthogonalGroup
    (g : spinGroup source9Quadratic) :
    ((source9SpinGammaOrthogonalHom g) : GammaMatrix) ∈
      Matrix.specialOrthogonalGroup SpinIndex ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨(source9SpinGammaOrthogonalHom g).property, ?_⟩
  rw [← gammaDetDirectHom_apply]
  exact gammaDetDirectHom_eq_one g

/-- The exact original-gamma Clifford representation as a single
global algebraic homomorphism from the genuine source Spin9 group
to the pinned special orthogonal matrix group SO(16). -/
noncomputable def source9SpinGammaSpecialOrthogonalHom :
    spinGroup source9Quadratic →*
      Matrix.specialOrthogonalGroup SpinIndex ℝ where
  toFun g :=
    ⟨((source9SpinGammaOrthogonalHom g) : GammaMatrix),
      source9SpinGammaMatrix_mem_specialOrthogonalGroup g⟩
  map_one' := by
    apply Subtype.ext
    change ((source9SpinGammaOrthogonalHom
      (1 : spinGroup source9Quadratic)) : GammaMatrix) = 1
    rw [map_one]
    rfl
  map_mul' := by
    intro g h
    apply Subtype.ext
    change ((source9SpinGammaOrthogonalHom (g * h)) : GammaMatrix) =
      ((source9SpinGammaOrthogonalHom g) : GammaMatrix) *
        ((source9SpinGammaOrthogonalHom h) : GammaMatrix)
    rw [map_mul]
    rfl

/-- The SO(16)-valued homomorphism has exactly the accepted
whole-Clifford original gamma evaluation. -/
theorem source9SpinGammaSpecialOrthogonalHom_apply
    (g : spinGroup source9Quadratic) :
    ((source9SpinGammaSpecialOrthogonalHom g) : GammaMatrix) =
      source9GammaCliffordAlgHom
        (g : CliffordAlgebra source9Quadratic) := by
  exact source9SpinGammaOrthogonalHom_apply g

#print axioms source9SpinGammaMatrix_mem_specialOrthogonalGroup
#print axioms source9SpinGammaSpecialOrthogonalHom
#print axioms source9SpinGammaSpecialOrthogonalHom_apply

end
end FCP.BFSSPairedSpin9Clifford
