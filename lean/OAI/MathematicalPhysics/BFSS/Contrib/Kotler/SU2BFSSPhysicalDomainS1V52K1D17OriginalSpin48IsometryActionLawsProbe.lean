import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D16OriginalSpin48QuadraticIsometryProbe

/-!
K1D17 — the group-action laws of the genuine original-source Spin48
quadratic isometries bundled in K1D16.

No surrogate inner product, no guessed representation, and no extra
axioms. Each equality is reduced by an explicit field-level/pointwise
bridge to the exact S1V31 source action, qualified by K1D11/K1D12.
For future elaboration problems, use typed/structure-field bridges
BEFORE changing compiler recursion/heartbeat limits.

We do not claim the source determinant is +1, image surjectivity,
an SO48 target, a covering, global Spin9, or BFSS spectra.
UNACCEPTED CANDIDATE pending exact owner strict compiler/axiom CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D17
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- The K1D16 isometry at the genuine source Spin identity is the
canonical identity isometry of the ORIGINAL source quadratic form. -/
theorem originalSourceSpin48QuadraticIsometry_one :
    FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry
      (1 : spinGroup Q) = QuadraticMap.IsometryEquiv.refl Q := by
  apply DFunLike.ext
  intro v
  change FCP.BFSSS1V31.sourceSpin48VectorAction
    (1 : spinGroup Q) v = v
  exact FCP.BFSSS1V52K1D11.originalSourceSpin48_one_trivialAction v

/-- Isometries of the original quadratic form compose in genuine
source Spin group multiplication order, with QuadraticMap trans
function composition performed right to left. -/
theorem originalSourceSpin48QuadraticIsometry_mul
    (s t : spinGroup Q) :
    FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry (s * t) =
      (FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry t).trans
        (FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s) := by
  apply DFunLike.ext
  intro v
  change FCP.BFSSS1V31.sourceSpin48VectorAction (s * t) v =
    FCP.BFSSS1V31.sourceSpin48VectorAction s
      (FCP.BFSSS1V31.sourceSpin48VectorAction t v)
  exact FCP.BFSSS1V52K1D12.originalSourceSpin48VectorAction_mul s t v

/-- The inverse of the K1D16 original quadratic isometry is
exactly the isometry induced by the genuine inverse source Spin element. -/
theorem originalSourceSpin48QuadraticIsometry_inv
    (s : spinGroup Q) :
    FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s⁻¹ =
      (FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s).symm := by
  apply DFunLike.ext
  intro v
  change FCP.BFSSS1V31.sourceSpin48VectorAction s⁻¹ v =
    FCP.BFSSS1V31.sourceSpin48VectorAction s⁻¹ v
  rfl

#print axioms originalSourceSpin48QuadraticIsometry_one
#print axioms originalSourceSpin48QuadraticIsometry_mul
#print axioms originalSourceSpin48QuadraticIsometry_inv

end
end FCP.BFSSS1V52K1D17
