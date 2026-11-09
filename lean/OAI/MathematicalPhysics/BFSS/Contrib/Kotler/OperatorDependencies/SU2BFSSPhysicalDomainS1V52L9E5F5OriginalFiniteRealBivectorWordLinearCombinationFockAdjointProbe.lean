import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F4OriginalCliffordFockStarRealScalarClosureProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F2OriginalFiniteBivectorWordFockStarAdjointProbe

/-!
S1V52L9E5F5 — RESEARCH CANDIDATE ONLY. NO ACCEPTED ROOTS.

Exact genuine original Clifford 48-real-source generators and
exact original Fock Hilbert adjoint. This candidate combines:
* F2: star-to-adjoint compatibility for every finite ordered word
  of original Clifford source *PAIRS*;
* F3: zero and conditional additivity on actual original Fock;
* F4: conditional compatibility for real scalar coefficients,
  ONLY IF F4 independently qualifies.

The resulting class is a finite REAL linear combination of
finite even-generator words, written using actual original
Clifford operations and no surrogate algebra. It is NOT a
proved characterization of the entire source even Clifford
subalgebra, and is NOT a proof of native Spin48 implementer
unitarity or a BFSS spectral theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F5
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F2
open FCP.BFSSS1V52L9E5F3
open FCP.BFSSS1V52L9E5F4

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev SourcePair := Source48Vector × Source48Vector

private abbrev sourceBivector (p : SourcePair) : C :=
  CliffordAlgebra.ι Q p.1 * CliffordAlgebra.ι Q p.2

private abbrev sourceEvenWord (ps : List SourcePair) : C :=
  (ps.map sourceBivector).prod

-- Keep this definition opaque in the large induction proof.
-- Its two recurrence equations are proved once, separately.
private def sourceEvenRealCombination
    (terms : List (ℝ × List SourcePair)) : C :=
  (terms.map (fun t => t.1 • sourceEvenWord t.2)).sum

private theorem sourceEvenRealCombination_nil :
    sourceEvenRealCombination ([] : List (ℝ × List SourcePair)) = (0 : C) := by
  simp only [sourceEvenRealCombination, List.map_nil, List.sum_nil]

private theorem sourceEvenRealCombination_cons
    (p : ℝ × List SourcePair) (ps : List (ℝ × List SourcePair)) :
    sourceEvenRealCombination (p :: ps) =
      p.1 • sourceEvenWord p.2 + sourceEvenRealCombination ps := by
  simp only [sourceEvenRealCombination, List.map_cons, List.sum_cons]

/-- The genuine original Clifford-to-Fock representation
intertwines source Clifford star and Fock Hilbert adjoint on
every finite real linear combination of finite ordered even
generator words. No global odd Clifford star preservation. -/
theorem originalFockCliffordAlgHom_star_finiteRealBivectorWordSum
    (terms : List (ℝ × List SourcePair)) :
    originalFockCliffordAlgHom
      (star (sourceEvenRealCombination terms)) =
    star (originalFockCliffordAlgHom
      (sourceEvenRealCombination terms)) := by
  induction terms with
  | nil =>
      rw [sourceEvenRealCombination_nil]
      exact originalFockCliffordAlgHom_star_zero
  | cons p ps ih =>
      have hword :
          originalFockCliffordAlgHom (star (sourceEvenWord p.2)) =
            star (originalFockCliffordAlgHom (sourceEvenWord p.2)) := by
        exact originalFockCliffordAlgHom_star_bivectorWord p.2
      have hscalar :
          originalFockCliffordAlgHom
              (star (p.1 • sourceEvenWord p.2)) =
            star (originalFockCliffordAlgHom
              (p.1 • sourceEvenWord p.2)) :=
        originalFockCliffordAlgHom_star_real_smul_of
          p.1 (sourceEvenWord p.2) hword
      rw [sourceEvenRealCombination_cons]
      exact originalFockCliffordAlgHom_star_add_of
        (p.1 • sourceEvenWord p.2)
        (sourceEvenRealCombination ps)
        hscalar ih

#print axioms originalFockCliffordAlgHom_star_finiteRealBivectorWordSum

end
end FCP.BFSSS1V52L9E5F5
