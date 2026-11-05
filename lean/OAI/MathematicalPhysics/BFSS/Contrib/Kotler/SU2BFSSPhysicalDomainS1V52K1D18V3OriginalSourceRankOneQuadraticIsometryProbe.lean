import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V2OriginalSourceRankOneInvolutionProbe

/-!
K1D18V3 — source-exact quadratic preservation for the actual original
48-dimensional Clifford-conjugation rank-one matrix.

First isolate a typed scalar/polarization identity on exactly the
accepted source form Q, then discharge its scalar premise using the
accepted B normalized source polar row. No surrogate inner product,
new labels, source reordering, or replacement Clifford action.

This is not unit normalization, Pin or Spin membership, source
reflection generation, surjectivity, topological covering, global
Spin9 covariance, or a BFSS spectrum claim.
All roots are CANDIDATES pending exact strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V3
noncomputable section
open FCP.BFSSS1V0
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Typed generic source-Q rank-one polarization cancellation.
The critical assumption is the actual scalar equality
c * Q(a) = polar(Q,a,v); no inversion or generator hypothesis
is hidden in this stage. -/
theorem source48Quadratic_smul_sub_preserve_of_polar_scaling
    (a v : Source48Vector) (c : ℝ)
    (hscale : c * Q a = QuadraticMap.polar Q a v) :
    Q (c • a - v) = Q v := by
  rw [sub_eq_add_neg,
    QuadraticMap.map_add (Q : Source48Vector → ℝ) (c • a) (-v),
    QuadraticMap.map_smul, QuadraticMap.map_neg,
    QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_left]
  simp only [smul_eq_mul]
  rw [← hscale]
  ring

/-- For the actual ORIGINAL source 48-vector and original normalized
polar row, the source-defined Clifford rank-one matrix preserves Q.
The source premise [Invertible (Q a)] is retained explicitly. -/
theorem source48_originalCliffordRankOne_preserves_quadratic
    (a v : Source48Vector) [Invertible (Q a)] :
    Q (FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
      (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) *ᵥ v) =
    Q v := by
  rw [FCP.BFSSS1V52K1D18C.source48_rankOneConjugationMatrix_mulVec,
    FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow_dot]
  apply source48Quadratic_smul_sub_preserve_of_polar_scaling
  calc
    (⅟(Q a) * QuadraticMap.polar Q a v) * Q a =
      (⅟(Q a) * Q a) * QuadraticMap.polar Q a v := by ring
    _ = (1 : ℝ) * QuadraticMap.polar Q a v := by rw [invOf_mul_self]
    _ = QuadraticMap.polar Q a v := by ring

#print axioms source48Quadratic_smul_sub_preserve_of_polar_scaling
#print axioms source48_originalCliffordRankOne_preserves_quadratic

end
end FCP.BFSSS1V52K1D18V3
