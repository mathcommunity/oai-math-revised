import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D14OriginalSpin48LinearRepresentationKernelProbe

/-!
K1D15 — exact original source Spin(48) action preserves its ORIGINAL
48-real quadratic form, without importing a surrogate inner product.

S1V31 defines the action by uniquely transporting Clifford generator
conjugation. K1D10 proves its exact Clifford-star formula.
K1D7 proves faithfulness of real scalar algebraMap into the original
Clifford algebra. Pinned Mathlib CliffordAlgebra.ι_sq_scalar equates
generator squares with the ORIGINAL source48Quadratic scalar values.

No determinant +1, target SO48, surjectivity, covering, global Spin9
lift or BFSS spectral claim is asserted. CANDIDATE pending strict CI.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace FCP.BFSSS1V52K1D15
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Exact original source Spin group Clifford conjugation fixes every
real scalar in the genuine source Clifford algebra. Uses only the
pinned Mathlib source Spin star-unitary law and algebraMap centrality. -/
theorem originalSourceSpin48_scalar_conjugation_fixed
    (s : spinGroup Q) (r : ℝ) :
    (s : C) * algebraMap ℝ C r * star (s : C) = algebraMap ℝ C r := by
  rw [← Algebra.commutes r (s : C), mul_assoc,
    spinGroup.mul_star_self_of_mem s.property, mul_one]

/-- The genuine ORIGINAL source Spin48 vector action preserves the
ORIGINAL source48Quadratic, for every source real 48-vector. -/
theorem originalSourceSpin48VectorAction_preserves_sourceQuadratic
    (s : spinGroup Q) (v : Source48Vector) :
    Q (FCP.BFSSS1V31.sourceSpin48VectorAction s v) = Q v := by
  let w : Source48Vector := FCP.BFSSS1V31.sourceSpin48VectorAction s v
  have hscalar : algebraMap ℝ C (Q w) = algebraMap ℝ C (Q v) := by
    calc
      algebraMap ℝ C (Q w) =
          CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q w :=
        (CliffordAlgebra.ι_sq_scalar Q w).symm
      _ =
          (ConjAct.toConjAct (spinGroup.toUnits s) • CliffordAlgebra.ι Q v) *
          (ConjAct.toConjAct (spinGroup.toUnits s) • CliffordAlgebra.ι Q v) := by
        simp only [w, FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator]
      _ = ConjAct.toConjAct (spinGroup.toUnits s) •
          (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v) := by
        exact (smul_mul' (ConjAct.toConjAct (spinGroup.toUnits s))
          (CliffordAlgebra.ι Q v) (CliffordAlgebra.ι Q v)).symm
      _ = ConjAct.toConjAct (spinGroup.toUnits s) •
          algebraMap ℝ C (Q v) := by
        rw [CliffordAlgebra.ι_sq_scalar]
      _ = algebraMap ℝ C (Q v) := by
        change (s : C) * algebraMap ℝ C (Q v) * star (s : C) =
          algebraMap ℝ C (Q v)
        exact originalSourceSpin48_scalar_conjugation_fixed s (Q v)
  have hquad : Q w = Q v := by
    apply FCP.BFSSS1V52K1D7.originalSourceClifford_algebraMap_injective
    exact hscalar
  simpa only [w] using hquad

#print axioms originalSourceSpin48_scalar_conjugation_fixed
#print axioms originalSourceSpin48VectorAction_preserves_sourceQuadratic

end
end FCP.BFSSS1V52K1D15
