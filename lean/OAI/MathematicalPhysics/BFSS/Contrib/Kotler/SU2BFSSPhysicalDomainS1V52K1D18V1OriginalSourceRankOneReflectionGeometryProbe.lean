import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18CRankOneActualCliffordGeneratorProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18UOriginalQuadraticNondegeneracyProbe

/-!
K1D18V1 — original-source rank-one Clifford reflection axis and
polar-orthogonal action. The original 48 labels, weighted-sum-squares
quadratic form, normalized polar row and actual rank-one source matrix
are reused verbatim from S1V0/K1D18B/C.

These are SOURCE-CONDITIONAL statements on invertible Q(a), and do not
construct a normalized source vector or a genuine Spin lift.
They do not prove image surjectivity, canonical SO48 equivalence,
topological covering, global Spin9 covariance, or BFSS spectra.
Theorems are CANDIDATES until the independent strict gate succeeds.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V1
noncomputable section
open FCP.BFSSS1V0
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- The actual source rank-one Clifford conjugation fixes its
defining original source vector (line-axis, not hyperplane, action). -/
theorem source48_original_reflection_fixes_axis
    (a : Source48Vector) [Invertible (Q a)] :
    FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
      (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) *ᵥ a = a := by
  rw [FCP.BFSSS1V52K1D18C.source48_rankOneConjugationMatrix_mulVec,
      FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow_dot_self]
  simp only [two_smul]
  abel

/-- On the exact kernel of the original normalized polar row, the
same original Clifford-conjugation matrix acts by negative identity. -/
theorem source48_original_reflection_negates_normalized_polar_kernel
    (a v : Source48Vector) [Invertible (Q a)]
    (hkernel :
      FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a ⬝ᵥ v = 0) :
    FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
      (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) *ᵥ v = -v := by
  rw [FCP.BFSSS1V52K1D18C.source48_rankOneConjugationMatrix_mulVec,
      hkernel]
  simp

/-- The negated hyperplane is defined by the ACTUAL original quadratic
polar form, not by an unspecified Euclidean surrogate. -/
theorem source48_original_reflection_negates_source_polar_orthogonal
    (a v : Source48Vector) [Invertible (Q a)]
    (hortho : QuadraticMap.polar Q a v = 0) :
    FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
      (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) *ᵥ v = -v := by
  apply source48_original_reflection_negates_normalized_polar_kernel a v
  rw [FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow_dot, hortho]
  simp

#print axioms source48_original_reflection_fixes_axis
#print axioms source48_original_reflection_negates_normalized_polar_kernel
#print axioms source48_original_reflection_negates_source_polar_orthogonal

end
end FCP.BFSSS1V52K1D18V1
