import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E1OriginalNativeSixteenSpin48UniversalCliffordConjugationProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG1APairedThetaProbe
import Mathlib.Tactic

/-!
S1V52L9E2 — UNQUALIFIED original-source *Fock* Clifford-generator
NORMALIZATION. The original original paired Majorana family obeys
the delta-one CAR, so individual pairedTheta operators square to
1/2. In contrast, the unit basis generators ι source48Quadratic
in the genuine original CliffordAlgebra square to 1.

Therefore the candidate Clifford-module generator on the ORIGINAL
Fermion 2 must be sqrt(2) * pairedTheta, not unscaled pairedTheta.

This gate tests only the exact single-axis normalization needed to
construct a future real Clifford-algebra representation. It does
NOT assert such an algebra homomorphism exists or is unitary or
that the original Fock gauge action is a Spin48 representation.
The original exact Fock pairing spinPairEquiv.symm α is retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000

namespace FCP.BFSSS1V52L9E2
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V5
open FCP.BFSSSU2GaugeG1A

/-- The candidate real-positive normalized original BFSS Fock
Majorana generator corresponding to the ACTUAL source block/color
axis; sqrt(2) is forced by delta-one source CAR. -/
noncomputable def originalNormalizedFockMajorana
    (α : RealSpinBlock) (A : Fin 3) :
    Fermion 2 →L[ℂ] Fermion 2 :=
  (↑(Real.sqrt 2) : ℂ) • pairedTheta (spinPairEquiv.symm α) A

/-- A unit source Majorana axis maps to a square-one operator
under the ORIGINAL Fock Majorana normalization, matching
CliffordAlgebra.ι source48Quadratic for Q(e)=1.
This is a preliminary generator-level theorem, NOT a proof
that a real Clifford algebra module has been constructed. -/
theorem originalNormalizedFockMajorana_sq_one
    (α : RealSpinBlock) (A : Fin 3) :
    originalNormalizedFockMajorana α A *
        originalNormalizedFockMajorana α A =
      (1 : Fermion 2 →L[ℂ] Fermion 2) := by
  let t : Fermion 2 →L[ℂ] Fermion 2 :=
    pairedTheta (spinPairEquiv.symm α) A
  have hcar : t * t + t * t =
      (1 : Fermion 2 →L[ℂ] Fermion 2) := by
    dsimp [t]
    simpa using (pairedTheta_CAR
      (spinPairEquiv.symm α) (spinPairEquiv.symm α) A A)
  -- The pinned Mathlib two_smul lemma converts the complex
  -- scalar 2 to the two identical ORIGINAL Fock operator products,
  -- directly matching the accepted delta-one CAR. Avoid rw
  -- [add_smul] on an already elaborated scalar expression.
  have hdouble : (2 : ℂ) • (t * t) =
      (1 : Fermion 2 →L[ℂ] Fermion 2) :=
    (two_smul ℂ (t * t)).trans hcar
  have hsqrt : ((↑(Real.sqrt 2) : ℂ) *
      (↑(Real.sqrt 2) : ℂ)) = (2 : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  change ((↑(Real.sqrt 2) : ℂ) • t) *
      ((↑(Real.sqrt 2) : ℂ) • t) = 1
  rw [smul_mul_smul, hsqrt]
  exact hdouble

#print axioms originalNormalizedFockMajorana_sq_one

end
end FCP.BFSSS1V52L9E2
