import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10BAOriginalGammaBracketDefectArbitrarySkewExtension
import Mathlib.Algebra.Lie.OfAssociative

/-!
K1D18V10H-F10BB — canonical native Mathlib
so(9,R) -> so(16,R) LieHom packaging.

F10AV qualified the exact original-gamma coefficient
LinearMap and proved that skew 9x9 inputs map into the
native Mathlib orthogonal Lie algebra so(16,R). F10BA
qualified bracket preservation for every pair of skew
source inputs. This stage packages exactly those accepted
facts into a genuine real Lie algebra homomorphism between
Mathlib's canonical orthogonal matrix Lie subalgebras.

The target is the original real 16x16 gamma carrier. The
distinct paired-48 line is not imported or used. Group
integration, covering, Fock, gauge, physical-domain, and
BFSS spectral claims remain separate.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The accepted original-gamma coefficient representation as
a genuine native Mathlib real Lie algebra homomorphism
so(9,R) -> so(16,R). -/
noncomputable def coordinateToOriginalGammaSkewLieHom :
    LieAlgebra.Orthogonal.so SpaceIndex ℝ →ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so SpinIndex ℝ where
  toFun := fun A =>
    ⟨coordinateToOriginalGammaLinearMap A.val,
      coordinateToOriginalGammaLinearMap_image_mem_so A.val
        (by
          have hA_mem := A.property
          rw [LieAlgebra.Orthogonal.mem_so] at hA_mem
          exact hA_mem)⟩
  map_add' := by
    intro A B
    apply Subtype.ext
    change coordinateToOriginalGammaLinearMap (A.val + B.val) =
      coordinateToOriginalGammaLinearMap A.val +
        coordinateToOriginalGammaLinearMap B.val
    exact map_add coordinateToOriginalGammaLinearMap A.val B.val
  map_smul' := by
    intro c A
    apply Subtype.ext
    change coordinateToOriginalGammaLinearMap (c • A.val) =
      c • coordinateToOriginalGammaLinearMap A.val
    exact map_smul coordinateToOriginalGammaLinearMap c A.val
  map_lie' := by
    intro A B
    apply Subtype.ext
    change coordinateToOriginalGammaLinearMap
        (A.val * B.val - B.val * A.val) =
      coordinateToOriginalGammaLinearMap A.val *
          coordinateToOriginalGammaLinearMap B.val -
        coordinateToOriginalGammaLinearMap B.val *
          coordinateToOriginalGammaLinearMap A.val
    have hA : A.val.transpose = -A.val := by
      have hA_mem := A.property
      rw [LieAlgebra.Orthogonal.mem_so] at hA_mem
      exact hA_mem
    have hB : B.val.transpose = -B.val := by
      have hB_mem := B.property
      rw [LieAlgebra.Orthogonal.mem_so] at hB_mem
      exact hB_mem
    exact sub_eq_zero.mp
      (coordinateToOriginalGammaBracketDefect_skew_pair_zero
        A.val B.val hA hB)

/-- Independent typed bracket specialization of the canonical
original-gamma Lie algebra homomorphism. -/
theorem coordinateToOriginalGammaSkewLieHom_map_lie
    (A B : LieAlgebra.Orthogonal.so SpaceIndex ℝ) :
    coordinateToOriginalGammaSkewLieHom ⁅A, B⁆ =
      ⁅coordinateToOriginalGammaSkewLieHom A,
        coordinateToOriginalGammaSkewLieHom B⁆ := by
  exact LieHom.map_lie coordinateToOriginalGammaSkewLieHom A B

#print axioms coordinateToOriginalGammaSkewLieHom
#print axioms coordinateToOriginalGammaSkewLieHom_map_lie

end
end FCP.BFSSPairedSpin9Clifford
