import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V33Original48SpinQuadraticIsometryProbe
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
S1V34 — actual original 48-real Clifford Spin group action packaged as
invertible REAL linear maps and quadratic-form-preserving equivalences.

Every action comes from the canonical S1V31 Clifford conjugation,
not from the original SU2->SO48 hom, a surrogate representation,
or a chosen Spin covering. Existence/injectivity, additivity, real
scalar linearity, group action and exact Q preservation are kernel
accepted in S1V29–S1V33.

NEW UNCOMPILED candidate until its own immutable strict gate qualifies
all THREE declarations. The quadratic isometry equivalences and
their reverse-order trans multiplication are prerequisites for, not
yet a packaged Spin→SO group hom with det +1 or a continuous cover.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V34
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V31

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Arbitrary genuine source-sized Spin48 Clifford conjugation defines
an invertible REAL-linear operator on the exact original 48-real
Majorana labels, with its inverse defined by the same actual action
of the inverse Spin element. -/
noncomputable def sourceSpin48LinearEquiv (s : spinGroup Q) :
    Source48Vector ≃ₗ[ℝ] Source48Vector where
  toFun := sourceSpin48VectorAction s
  invFun := sourceSpin48VectorAction s⁻¹
  left_inv := by
    intro v
    change sourceSpin48VectorAction s⁻¹ (sourceSpin48VectorAction s v) = v
    rw [← FCP.BFSSS1V32.sourceSpin48VectorAction_mul,
      inv_mul_cancel, FCP.BFSSS1V32.sourceSpin48VectorAction_one]
  right_inv := by
    intro v
    change sourceSpin48VectorAction s (sourceSpin48VectorAction s⁻¹ v) = v
    rw [← FCP.BFSSS1V32.sourceSpin48VectorAction_mul,
      mul_inv_cancel, FCP.BFSSS1V32.sourceSpin48VectorAction_one]
  map_add' := FCP.BFSSS1V31.sourceSpin48VectorAction_add s
  map_smul' := FCP.BFSSS1V32.sourceSpin48VectorAction_smul s

/- Every genuine source Spin48 element acts via an invertible linear
equivalence which preserves EXACTLY the original real source quadratic
form Q on Fin24 x Fin2 labels. No hypothetical projection needed. -/
-- Constrain the larger elaboration budget to the packaging declaration,
-- not to the accepted original math or the entire Lean module.
set_option maxRecDepth 2048 in
noncomputable def sourceSpin48QuadraticIsometryEquiv (s : spinGroup Q) :
    Q.IsometryEquiv Q := by
  let e : Source48Vector ≃ₗ[ℝ] Source48Vector := sourceSpin48LinearEquiv s
  have hQ : ∀ v : Source48Vector, Q (e v) = Q v := by
    intro v
    change Q (sourceSpin48VectorAction s v) = Q v
    exact FCP.BFSSS1V33.sourceSpin48VectorAction_preserves_sourceQ s v
  exact { e with map_app' := hQ }

/-- Composition of original source quadratic isometries follows the
ACTUAL Spin-group multiplication in the correct order: first t then s.
This avoids falsely interpreting IsometryEquiv.trans as multiplication
in the wrong order. -/
theorem sourceSpin48QuadraticIsometryEquiv_mul
    (s t : spinGroup Q) :
    sourceSpin48QuadraticIsometryEquiv (s * t) =
      (sourceSpin48QuadraticIsometryEquiv t).trans
        (sourceSpin48QuadraticIsometryEquiv s) := by
  apply DFunLike.ext
  intro v
  change sourceSpin48VectorAction (s * t) v =
    sourceSpin48VectorAction s (sourceSpin48VectorAction t v)
  exact FCP.BFSSS1V32.sourceSpin48VectorAction_mul s t v

#print axioms sourceSpin48LinearEquiv
#print axioms sourceSpin48QuadraticIsometryEquiv
#print axioms sourceSpin48QuadraticIsometryEquiv_mul

end
end FCP.BFSSS1V34
