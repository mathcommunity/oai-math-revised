import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10AIOriginalGammaAllOrderedPairsLinearIndependentBridge
import Mathlib.Algebra.Lie.Classical

/-!
K1D18V10H-F10AJ — exact ORIGINAL gamma-pair embedding
into Mathlib's native orthogonal Lie algebra so(16,R).

F10AI established official Mathlib LinearIndependent for all
36 canonical (a<b) products of the actual nine public
sixteen-real source gamma matrices.

This bounded bridge shows these matrices are skew-symmetric
using the accepted ORIGINAL source gamma_symmetric and
source9OriginalGamma_anticommute, places them in the pinned
Mathlib native LieAlgebra.Orthogonal.so SpinIndex ℝ,
and transports F10AI's 36-word LinearIndependent predicate
to that actual LieSubalgebra.

The scalar-coefficient span of 36 gamma-pairs is therefore
a 36-dimensionally independent family INSIDE the actual
so(16,R) Lie algebra. No LieHom from so(9) has been
constructed yet; the Lie bracket relations are a future
independent gate. No global Spin(9) action or Spin(48)
lift, Fock construction, spectral or BFSS physical
conclusion is claimed.

No private source gamma tables, replacement matrices,
surrogate Clifford carriers, axioms, admits, or increased
Lean resource limits. CANDIDATE until fresh strict compiler
and all three independent theorem declaration/axiom checks.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open OAI.BFSSQuantum
open Matrix

/-- Canonical ORIGINAL gamma pair products are skew-
symmetric since each original gamma is symmetric and
distinct source gamma factors anticommute. -/
theorem source9OriginalGamma_ordered_pair_transpose_neg
    (p : Source9OrderedGammaPairIndex) :
    (source9OrderedGammaPairMatrix p).transpose =
      -(source9OrderedGammaPairMatrix p) := by
  change (gamma p.val.1 * gamma p.val.2).transpose =
    -(gamma p.val.1 * gamma p.val.2)
  rw [Matrix.transpose_mul]
  rw [gamma_symmetric p.val.2, gamma_symmetric p.val.1]
  exact source9OriginalGamma_anticommute
    p.val.2 p.val.1 (ne_of_gt p.property)

/-- Canonical gamma pair products from the ORIGINAL source
lie inside Mathlib's NATIVE definite orthogonal Lie
subalgebra of 16-by-16 real matrices. -/
theorem source9OriginalGamma_ordered_pair_mem_so
    (p : Source9OrderedGammaPairIndex) :
    source9OrderedGammaPairMatrix p ∈
      LieAlgebra.Orthogonal.so SpinIndex ℝ := by
  rw [LieAlgebra.Orthogonal.mem_so]
  exact source9OriginalGamma_ordered_pair_transpose_neg p

/-- Same original matrix, now treated as a member of
Mathlib's native orthogonal Lie subalgebra. -/
def source9OrderedGammaPairInSo
    (p : Source9OrderedGammaPairIndex) :
    LieAlgebra.Orthogonal.so SpinIndex ℝ :=
  ⟨source9OrderedGammaPairMatrix p,
   source9OriginalGamma_ordered_pair_mem_so p⟩

/-- The native orthogonal Lie subalgebra inclusion as a
real-linear map; no alternate representation or LieHom
is assumed here. -/
private def source9SoValLinear :
    LieAlgebra.Orthogonal.so SpinIndex ℝ →ₗ[ℝ] GammaMatrix :=
  { toFun := fun x => (x : GammaMatrix)
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl }

/-- OFFICIAL Mathlib LinearIndependent of the 36 actual
source gamma-pair elements inside the native orthogonal
Lie subalgebra, via the inclusion to the original source
real-matrix carrier and the qualified F10AI theorem. -/
theorem source9OriginalGamma_ordered_pairs_so_linearIndependent :
    LinearIndependent ℝ source9OrderedGammaPairInSo := by
  apply LinearIndependent.of_comp source9SoValLinear
  simpa [Function.comp_def, source9SoValLinear,
    source9OrderedGammaPairInSo] using
    source9OriginalGamma_all_ordered_pairs_linearIndependent

#print axioms source9OriginalGamma_ordered_pair_transpose_neg
#print axioms source9OriginalGamma_ordered_pair_mem_so
#print axioms source9OriginalGamma_ordered_pairs_so_linearIndependent

end
end FCP.BFSSPairedSpin9Clifford
