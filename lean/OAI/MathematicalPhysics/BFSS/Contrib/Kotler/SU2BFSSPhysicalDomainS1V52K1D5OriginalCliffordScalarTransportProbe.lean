import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D4OriginalSpin48ExteriorScalarKernel

/-!
K1D5 — source-exact Clifford scalar transport.

The pinned Mathlib CliffordAlgebra.changeForm_algebraMap theorem ensures
equivExterior (a REAL-linear equivalence, NOT an algebra equivalence)
maps the source Clifford scalar line to the actual exterior scalar line.
Injectivity then transports K1D4's proven exterior scalar conclusion
back to the exact original 48-real source Clifford algebra.

This alone does NOT classify which scalars belong to spinGroup, nor
prove a two-sign Spin(48) kernel, covering, global Spin(9), or spectra.
CANDIDATE pending new independent strict Lean/axiom qualification.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52K1D5
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev E := ExteriorAlgebra ℝ Source48Vector

/-- The genuine source Clifford-to-exterior real-linear equivalence
preserves the scalar algebraMap exactly. No product preservation asserted. -/
theorem originalSource_equivExterior_algebraMap (c : ℝ) :
    (CliffordAlgebra.equivExterior Q) (algebraMap ℝ C c) =
      algebraMap ℝ E c := by
  simpa only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply] using
    (CliffordAlgebra.changeForm_algebraMap
      (h := CliffordAlgebra.changeForm.associated_neg_proof (Q := Q)) c)

/-- Every original Spin(48) element acting trivially on every
original source vector is an actual Clifford scalar. This theorem
does not assert the scalar equals 1 or -1. -/
theorem originalSourceSpin48_trivialAction_clifford_scalar
    (s : spinGroup Q)
    (hs : ∀ v : Source48Vector,
      FCP.BFSSS1V31.sourceSpin48VectorAction s v = v) :
    ∃ c : ℝ, (s : C) = algebraMap ℝ C c := by
  obtain ⟨c, hc⟩ :=
    FCP.BFSSS1V52K1D4.originalSourceSpin48_trivialAction_exterior_scalar s hs
  refine ⟨c, ?_⟩
  apply (CliffordAlgebra.equivExterior Q).injective
  exact hc.trans (originalSource_equivExterior_algebraMap c).symm

#print axioms originalSource_equivExterior_algebraMap
#print axioms originalSourceSpin48_trivialAction_clifford_scalar

end
end FCP.BFSSS1V52K1D5
