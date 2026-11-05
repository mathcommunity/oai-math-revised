import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10DBDerivativeRangeCommutatorClosure
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative

/-!
F10DC: package the actual original Clifford derivative range as a Lie subalgebra,
then package the existing native real-linear equivalence as a Lie equivalence.

The only new closure input is F10DB's exact ambient commutator-closure theorem.
No associative/unital subalgebra, source tangent identification, manifold differential,
or global Spin(9) integration is asserted.
-/
set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSGamma9

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual identity-chart derivative range, with its ambient Clifford commutator bracket. -/
noncomputable def source9IdentityChartDerivativeLieSubalgebra :
    LieSubalgebra ℝ (CliffordAlgebra source9Quadratic) :=
  { source9IdentityChartDerivativeRange with
    lie_mem' := by
      intro x y hx hy
      change x * y - y * x ∈ source9IdentityChartDerivativeRange
      exact source9IdentityChartDerivativeRange_commutator_mem ⟨x, hx⟩ ⟨y, hy⟩
  }

/-- The existing native real-linear range equivalence, now preserving the actual Lie brackets. -/
noncomputable def source9NativeSkewDerivativeRangeLieEquiv :
    LieAlgebra.Orthogonal.so SpaceIndex ℝ ≃ₗ⁅ℝ⁆
      source9IdentityChartDerivativeLieSubalgebra where
  toFun := fun A =>
    ⟨(source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic), by
      change (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) ∈
        source9IdentityChartDerivativeRange
      exact (source9NativeSkewDerivativeRangeEquiv A).property⟩
  map_add' := by
    intro A B
    apply Subtype.ext
    exact congrArg (fun z : source9IdentityChartDerivativeRange =>
      (z : CliffordAlgebra source9Quadratic))
      (map_add source9NativeSkewDerivativeRangeEquiv A B)
  map_smul' := by
    intro r A
    apply Subtype.ext
    exact congrArg (fun z : source9IdentityChartDerivativeRange =>
      (z : CliffordAlgebra source9Quadratic))
      (map_smul source9NativeSkewDerivativeRangeEquiv r A)
  map_lie' := by
    intro A B
    apply Subtype.ext
    change (source9NativeSkewDerivativeRangeEquiv ⁅A, B⁆ :
        CliffordAlgebra source9Quadratic) =
      (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic) *
          (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) -
        (source9NativeSkewDerivativeRangeEquiv B : CliffordAlgebra source9Quadratic) *
          (source9NativeSkewDerivativeRangeEquiv A : CliffordAlgebra source9Quadratic)
    exact (source9NativeSkewDerivativeRangeEquiv_commutator A B).symm
  invFun := fun x =>
    source9NativeSkewDerivativeRangeEquiv.symm
      ⟨(x : CliffordAlgebra source9Quadratic), by
        exact x.property⟩
  left_inv := by
    intro A
    exact source9NativeSkewDerivativeRangeEquiv.left_inv A
  right_inv := by
    intro x
    apply Subtype.ext
    let y : source9IdentityChartDerivativeRange :=
      ⟨(x : CliffordAlgebra source9Quadratic), by
        exact x.property⟩
    exact congrArg (fun z : source9IdentityChartDerivativeRange =>
      (z : CliffordAlgebra source9Quadratic))
      (source9NativeSkewDerivativeRangeEquiv.right_inv y)

#print axioms source9IdentityChartDerivativeLieSubalgebra
#print axioms source9NativeSkewDerivativeRangeLieEquiv

end
end FCP.BFSSPairedSpin9Clifford
