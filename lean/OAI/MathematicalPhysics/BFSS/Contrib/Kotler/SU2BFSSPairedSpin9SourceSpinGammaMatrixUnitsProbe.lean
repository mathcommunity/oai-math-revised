import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9SourceCliffordGammaLiftProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Algebra.Group.Units.Hom

/-!
K1D18V10D — algebraic restriction of the genuine nine-source
Clifford gamma representation to the ACTUAL pinned Mathlib
spinGroup source9Quadratic.

This constructs a single, coherent group homomorphism from
spinGroup source9Quadratic into invertible original real 16x16
gamma matrices. The proof uses the actual source Cl(9) AlgHom,
the pinned spinGroup.toUnits and Units.map interfaces.
No substitute source group, gamma basis, or hidden kernel is used.

The target is GammaMatrixˣ, i.e. algebraic invertible matrices.
This does NOT prove orthogonality, SO(16), an original paired
SO(48) representation, topology/continuity, the central sign,
a Spin48 covering, source Fock action, or BFSS spectral physics.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum

/-- A genuine *global algebraic group homomorphism* from the
actual pinned source Spin(9) subtype to units of the exact
accepted 16-real-gamma matrix algebra. Unlike V10B, its
domain is the entire source spinGroup, not Multiplicative ℝ. -/
noncomputable def source9SpinGammaMatrixUnitsHom :
    spinGroup source9Quadratic →* GammaMatrixˣ :=
  (Units.map (source9GammaCliffordAlgHom :
      CliffordAlgebra source9Quadratic →* GammaMatrix)).comp
    (spinGroup.toUnits (Q := source9Quadratic))

/-- The new full-source Spin(9) action evaluates to the
original accepted Clifford algebra homomorphism, with no
replacement for the nine real gamma signed permutations. -/
theorem source9SpinGammaMatrixUnitsHom_apply
    (g : spinGroup source9Quadratic) :
    ((source9SpinGammaMatrixUnitsHom g) : GammaMatrix) =
      source9GammaCliffordAlgHom
        (g : CliffordAlgebra source9Quadratic) := rfl

/-- Invertibility of the actual matrix image of every element
of the source Spin(9), via the explicit typed group homomorphism. -/
theorem source9SpinGammaMatrix_isUnit
    (g : spinGroup source9Quadratic) :
    IsUnit (source9GammaCliffordAlgHom
      (g : CliffordAlgebra source9Quadratic)) := by
  rw [← source9SpinGammaMatrixUnitsHom_apply g]
  exact Units.isUnit (source9SpinGammaMatrixUnitsHom g)

#print axioms source9SpinGammaMatrixUnitsHom
#print axioms source9SpinGammaMatrixUnitsHom_apply
#print axioms source9SpinGammaMatrix_isUnit

end
end FCP.BFSSPairedSpin9Clifford
