import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K8E3CoreNoncancellationProbe

/-!
# BFSS SU(2) G4-K9A — exact source coefficient crosswalk, first stage

UNCOMPILED CANDIDATE until the pinned compiler accepts the exact source SHA.

Compare only the actual BFSS source `deformedPotentialMatrix 1 0` and
`deformedPotentialCoefficients 1 0` against the original color bracket and
Clifford-pair entries. The mass term vanishes; the source matrix carries
a leading minus sign, while the genuine Clifford pair is skew under transpose.

These are necessary identities for the proposed `deformedCoreCharge 1 0 = charge`
crosswalk; they are NOT yet the full operator equality, form equality,
closed-form domain identity, a Hamiltonian spectral theorem or a mass-gap result.
-/

namespace FCP.BFSSSU2GaugeG4K9A
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open Finset Matrix

/-- The literal source deformed potential matrix at h=1,m=0 is the
negative pair-gamma contraction, with NO mass term, for arbitrary
source AlgebraData N. This is a definitional comparison. -/
theorem sourceMasslessPotentialMatrix_eq_neg_pairSum
    {N : ℕ} (M : AlgebraData N) (x : Boson N) (A : ColorIndex N) :
    M.deformedPotentialMatrix 1 0 x A =
      -(∑ p : BFSSGamma.SpatialPair,
        (M.coordinateBracket x p A) • BFSSGamma.pairGamma M.gamma p) := by
  simp [deformedPotentialMatrix, BFSSGamma.bracketMassMatrix]

/-- A genuine, source-typed Clifford-pair transpose converts the negative
massless matrix's beta-alpha entry to the POSITIVE alpha-beta coefficient.
No abstract surrogate gamma matrix or invented symmetry axiom is used. -/
theorem sourceMasslessPotentialCoefficient_eq_pairSum
    {N : ℕ} (M : AlgebraData N) (x : Boson N)
    (α β : SpinIndex) (A : ColorIndex N) :
    M.deformedPotentialCoefficients 1 0 x α (β, A) =
      ∑ p : BFSSGamma.SpatialPair,
        M.coordinateBracket x p A *
          BFSSGamma.pairGamma M.gamma p α β := by
  have hskew (p : BFSSGamma.SpatialPair) :
      BFSSGamma.pairGamma M.gamma p β α =
        -BFSSGamma.pairGamma M.gamma p α β := by
    have hs := BFSSGamma.pairGamma_skew
      M.gamma M.gamma_clifford M.gamma_symmetric p
    have he := congrArg (fun P : GammaMatrix => P α β) hs
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using he
  change M.deformedPotentialMatrix 1 0 x A β α = _
  rw [sourceMasslessPotentialMatrix_eq_neg_pairSum M x A]
  simp only [Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp [hskew, mul_neg, Finset.sum_neg_distrib]

#print axioms sourceMasslessPotentialMatrix_eq_neg_pairSum
#print axioms sourceMasslessPotentialCoefficient_eq_pairSum

end
end FCP.BFSSSU2GaugeG4K9A
