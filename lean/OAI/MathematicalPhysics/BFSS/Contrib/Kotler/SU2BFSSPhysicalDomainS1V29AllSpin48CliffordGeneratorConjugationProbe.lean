import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V0StandaloneOrthogonalGeometryProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-! Owner import from FCP cc608e2282e1b32bb11bbb64424e4775b28138e2,
original source blob 2483cb5646b8df2b5958cee2d02769de2018ab7f.
Only imports and this provenance comment are adapted. Definitions, theorem
statements and proof bodies below are source-exact. Local candidate only
until an independent owner strict gate passes. -/

/-!
S1V29 — ACTUAL SOURCE-SIZED all-Spin48 Clifford-generator interface.

This is not another test of the fixed sixteen-rotor quarter turn. It
instantiates the pinned Mathlib arbitrary-Spin-group Clifford conjugation
theorems for EVERY s : spinGroup source48Quadratic and EVERY 48-real
source vector, in the same cached environment as the original S1K–S1M
continuous SU2→SO48 representation.

The third root makes the intrinsic central-sign ambiguity exact for
Clifford conjugation: the words s and -s act identically. This is the
reason a real 48×48 SO action cannot determine the Spin lift's sign.

UNCOMPILED CANDIDATE until immutable source and strict CI qualify all
roots. It does NOT prove Clifford ι injectivity, define a Spin48→SO48
projection, prove Q-preservation/det-one or a covering, or construct a
continuous SU2→Spin48 homomorphism or manuscript Hilbert intertwiner.
-/

set_option autoImplicit false
set_option maxHeartbeats 280000

namespace FCP.BFSSS1V29
noncomputable section

open FCP.BFSSS1V0
open scoped Pointwise

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Every actual source-sized Spin(48) element acts on EVERY actual
source 48-real generator through another element in the image of the
very same Clifford ι, with no SU2 surrogate or quarter premise. -/
theorem all_sourceSpin48_generators_stay_real
    (s : spinGroup Q) (v : Source48Vector) :
    ConjAct.toConjAct (spinGroup.toUnits s) •
        (CliffordAlgebra.ι Q v) ∈
      LinearMap.range (CliffordAlgebra.ι Q) := by
  have hs : ((spinGroup.toUnits s : Cˣ) : C) ∈ spinGroup Q := by
    change (s : C) ∈ spinGroup Q
    exact s.property
  exact spinGroup.conjAct_smul_ι_mem_range_ι hs v

/-- The full original 48-real generator subspace is preserved as an
equality, not merely a one-sided image containment, by EVERY Spin(48)
element. This is a precursor to — not the construction of — its SO
representation. -/
theorem all_sourceSpin48_real_generator_space_preserved
    (s : spinGroup Q) :
    ConjAct.toConjAct (spinGroup.toUnits s) •
        LinearMap.range (CliffordAlgebra.ι Q) =
      LinearMap.range (CliffordAlgebra.ι Q) := by
  have hs : ((spinGroup.toUnits s : Cˣ) : C) ∈ spinGroup Q := by
    change (s : C) ∈ spinGroup Q
    exact s.property
  exact spinGroup.conjAct_smul_range_ι hs

/-- A direct source-sized Clifford identity displaying the unavoidable
central-sign blindness of the real orthogonal action. It does not claim
that an unqualified -s is already a chosen normalized group lift. -/
theorem sourceSpin48_conjugation_central_sign_invariant
    (s : spinGroup Q) (x : C) :
    (-(s : C)) * x * star (-(s : C)) =
      (s : C) * x * star (s : C) := by
  simp only [star_neg, neg_mul, mul_neg, neg_neg]

#print axioms all_sourceSpin48_generators_stay_real
#print axioms all_sourceSpin48_real_generator_space_preserved
#print axioms sourceSpin48_conjugation_central_sign_invariant

end
end FCP.BFSSS1V29
