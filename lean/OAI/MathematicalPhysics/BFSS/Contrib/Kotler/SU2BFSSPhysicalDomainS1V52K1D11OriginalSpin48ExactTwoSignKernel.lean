import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D10OriginalSpin48NegativeCentralTrivialActionProbe

/-!
K1D11 — exact TWO-SIGN POINTWISE KERNEL of the original Spin(48)
action on the ORIGINAL Source48Vector = Fin 24 × Fin 2 → ℝ.

This only composes the independently qualified source-exact K1D8
upper bound, K1D9 actual negative central membership, and K1D10
real-vector triviality of that element. K1D7 provides distinctness.

We prove exact pointwise stabilizer equality. We do NOT assert a
previously unconstructed Spin→SO group homomorphism, a topological
covering, a global Spin(9) lift, or any BFSS spectral existence.
CANDIDATE until strict owner compiler and axioms verification pass.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace FCP.BFSSS1V52K1D11
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- The genuine negative-central Spin48 element from accepted K1D9. -/
def originalSourceNegativeCentral : spinGroup Q :=
  ⟨(-1 : C), FCP.BFSSS1V52K1D9.originalSourceSpin48_neg_one_mem⟩

/-- The identity in the actual source Spin group fixes every original
real source vector under the S1V31 action. -/
theorem originalSourceSpin48_one_trivialAction :
    ∀ v : Source48Vector,
      FCP.BFSSS1V31.sourceSpin48VectorAction (1 : spinGroup Q) v = v := by
  intro v
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  rw [FCP.BFSSS1V52K1D10.originalSourceSpin48VectorAction_clifford_star]
  simp

/-- Exact group-element characterization of the original source
pointwise stabilizer: only the identity and the constructed genuine
negative-central Spin element fix all source 48-real generators. -/
theorem originalSourceSpin48_trivialAction_iff_two_signs
    (s : spinGroup Q) :
    (∀ v : Source48Vector,
        FCP.BFSSS1V31.sourceSpin48VectorAction s v = v) ↔
      s = 1 ∨ s = originalSourceNegativeCentral := by
  constructor
  · intro hs
    rcases
      FCP.BFSSS1V52K1D8.originalSourceSpin48_trivialAction_clifford_one_or_neg_one s hs
      with hpos | hneg
    · left
      apply Subtype.ext
      simpa using hpos
    · right
      apply Subtype.ext
      exact hneg
  · rintro (rfl | rfl)
    · exact originalSourceSpin48_one_trivialAction
    · exact FCP.BFSSS1V52K1D10.originalSourceSpin48_negativeCentral_trivialAction

/-- Set equality for the *pointwise stabilizer* of the ACTUAL source
Spin48 vector action, not an unconstructed Spin→SO homomorphism kernel. -/
theorem originalSourceSpin48_pointwiseKernel_eq_two_sign_set :
    {s : spinGroup Q |
      ∀ v : Source48Vector,
        FCP.BFSSS1V31.sourceSpin48VectorAction s v = v} =
      ({1, originalSourceNegativeCentral} : Set (spinGroup Q)) := by
  ext s
  simpa only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] using
    (originalSourceSpin48_trivialAction_iff_two_signs s)

/-- The two genuine group elements in the exact kernel really are
distinct, using the accepted faithful original Clifford scalar map. -/
theorem originalSourceSpin48_one_ne_negativeCentral :
    (1 : spinGroup Q) ≠ originalSourceNegativeCentral := by
  intro h
  have hc : (1 : C) = (-1 : C) := by
    have h' := congrArg (fun t : spinGroup Q => (t : C)) h
    simpa only [originalSourceNegativeCentral, Submonoid.coe_one] using h'
  have hr : (1 : ℝ) = (-1 : ℝ) :=
    FCP.BFSSS1V52K1D7.originalSourceClifford_algebraMap_injective 1 (-1)
      (by simpa using hc)
  norm_num at hr

#print axioms originalSourceSpin48_one_trivialAction
#print axioms originalSourceSpin48_trivialAction_iff_two_signs
#print axioms originalSourceSpin48_pointwiseKernel_eq_two_sign_set
#print axioms originalSourceSpin48_one_ne_negativeCentral

end
end FCP.BFSSS1V52K1D11
