import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D6OriginalSpin48ScalarStarNormProbe

/-!
K1D7 — recover the real scalar coefficient norm from the original
Spin(48) Clifford algebra, without a guessed representation.

Pinned Mathlib's ExteriorAlgebra.algebraMap_inj establishes that scalar
inclusion into the actual original exterior algebra is injective.
Accepted K1D5's exact source equivExterior scalar compatibility then
transports that faithfulness to the actual original Clifford algebra.

K1D6 supplies square-one INSIDE Clifford; this lemma now proves
c*c = 1 INSIDE REALS. It does NOT yet classify the two signs or
establish negative-central Spin membership and the full group kernel.
CANDIDATE ONLY pending exact fresh owner strict CI and axiom audit.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52K1D7
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev E := ExteriorAlgebra ℝ Source48Vector

/-- The actual source Clifford algebra has a faithful real scalar
embedding, via the scalar-preserving real-linear equivExterior map
and Mathlib's genuine exterior algebraMap left inverse. -/
theorem originalSourceClifford_algebraMap_injective (a b : ℝ)
    (h : algebraMap ℝ C a = algebraMap ℝ C b) : a = b := by
  have hE : algebraMap ℝ E a = algebraMap ℝ E b := by
    have h' := congrArg (CliffordAlgebra.equivExterior Q) h
    simpa only [
      FCP.BFSSS1V52K1D5.originalSource_equivExterior_algebraMap] using h'
  exact (ExteriorAlgebra.algebraMap_inj (M := Source48Vector) a b).mp hE

/-- The real scalar coefficient of every original Spin(48) element
in the original source vector-action kernel satisfies c*c = 1.
No coefficient sign is selected or asserted to be represented here. -/
theorem originalSourceSpin48_trivialAction_clifford_scalar_coefficient_square_one
    (s : spinGroup Q)
    (hs : ∀ v : Source48Vector,
      FCP.BFSSS1V31.sourceSpin48VectorAction s v = v) :
    ∃ c : ℝ, (s : C) = algebraMap ℝ C c ∧ c * c = 1 := by
  obtain ⟨c, hc⟩ :=
    FCP.BFSSS1V52K1D5.originalSourceSpin48_trivialAction_clifford_scalar s hs
  refine ⟨c, hc, ?_⟩
  have hsq :=
    FCP.BFSSS1V52K1D6.originalSourceSpin48_trivialAction_clifford_square_eq_one s hs
  rw [hc] at hsq
  have hmap : algebraMap ℝ C (c * c) = algebraMap ℝ C (1 : ℝ) := by
    simpa only [map_mul, map_one] using hsq
  exact originalSourceClifford_algebraMap_injective (c * c) 1 hmap

#print axioms originalSourceClifford_algebraMap_injective
#print axioms originalSourceSpin48_trivialAction_clifford_scalar_coefficient_square_one

end
end FCP.BFSSS1V52K1D7
