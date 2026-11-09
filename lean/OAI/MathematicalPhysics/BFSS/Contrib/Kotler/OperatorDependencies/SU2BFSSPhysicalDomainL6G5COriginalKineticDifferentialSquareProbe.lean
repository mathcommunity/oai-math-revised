import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5BOriginalComplexKineticColorGramProbe

/-!
# L6G5C — original-source kinetic differential square from qualified Gram

This gate composes the exact -i complex kinetic weights of L6G5B with
the original coordinateDerivative operators, using only finite sums and
module-endomorphism algebra. All source-specific hypotheses are discharged
by L6G5B's accepted color Gram theorem.

The scalar diagonal second-derivative sum is literally built from the
pinned original source coordinateDerivative, not a substituted Laplacian.
The separate identification with the kinetic part of the full
normal-ordered coefficient square, the potential, and both Gauss terms
remain subsequent tasks. No spectral or physical-domain claim.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G5C
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G2
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G5B
open FCP.BFSSSU2PhysicalDomainL6G1

/-- A finite Gram identity contracts the square of a genuinely
operator-valued finite linear combination. The lemma has no assumed
commutativity of operators and no physical or gamma premises. -/
private theorem weightedOperatorGramSquare
    {R I J : Type*} [Ring R] [Algebra ℂ R]
    [Fintype I] [Fintype J] [DecidableEq I]
    (K : J → I → ℂ) (D : I → R) (g : ℂ)
    (hGram : ∀ u v : I,
      (∑ p : J, K p u * K p v) = if u = v then g else 0) :
    (∑ p : J, (∑ u : I, K p u • D u) *
      (∑ v : I, K p v • D v)) =
        g • (∑ u : I, D u * D u) := by
  classical
  have hexpand (p : J) :
      (∑ u : I, K p u • D u) * (∑ v : I, K p v • D v) =
        ∑ u : I, ∑ v : I, (K p u * K p v) • (D u * D v) := by
    calc
      _ = ∑ u : I, (K p u • D u) * (∑ v : I, K p v • D v) := by
        rw [Finset.sum_mul]
      _ = ∑ u : I, ∑ v : I, (K p u • D u) * (K p v • D v) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [mul_comm (K p v) (K p u)]
  calc
    _ = ∑ p : J, ∑ u : I, ∑ v : I,
          (K p u * K p v) • (D u * D v) := by
      apply Finset.sum_congr rfl
      intro p _
      exact hexpand p
    _ = ∑ u : I, ∑ p : J, ∑ v : I,
          (K p u * K p v) • (D u * D v) := Finset.sum_comm
    _ = ∑ u : I, ∑ v : I, ∑ p : J,
          (K p u * K p v) • (D u * D v) := by
      apply Finset.sum_congr rfl
      intro u _
      exact Finset.sum_comm
    _ = ∑ u : I, ∑ v : I,
          (∑ p : J, K p u * K p v) • (D u * D v) := by
      simp only [← Finset.sum_smul]
    _ = ∑ u : I, ∑ v : I,
          (if u = v then g else 0) • (D u * D v) := by
      simp_rw [hGram]
    _ = ∑ u : I, g • (D u * D u) := by
      apply Finset.sum_congr rfl
      intro u _
      simp
    _ = _ := by rw [Finset.smul_sum]

/-- Original -i weighted differential operator for a single actual
fermion label. No replacement representation or change in normalization. -/
def sourceSpinorKineticDifferential {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) (p : FermionLabel N) : SourceEnd N :=
  ∑ u : BosonLabel N,
    sourceSpinorKineticWeight M w p u • sourceD u

/-- Original smooth-core source Laplacian differential expression:
the literal sum of original coordinate derivative squares. -/
def sourceOriginalSecondDerivativeSum {N : ℕ} : SourceEnd N :=
  ∑ u : BosonLabel N, sourceD u * sourceD u

/-- Complete finite source kinetic differential square. The Gram
premise is the exact L6G5B theorem, not an added source assumption.
The only explicit premise identifies the source gamma field. -/
theorem sourceSpinorKineticDifferential_square {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (hgamma : M.gamma = originalGamma) :
    (∑ p : FermionLabel N,
      sourceSpinorKineticDifferential M w p *
      sourceSpinorKineticDifferential M w p) =
        -(spinorSquareNorm w : ℂ) •
          sourceOriginalSecondDerivativeSum (N := N) := by
  unfold sourceSpinorKineticDifferential sourceOriginalSecondDerivativeSum
  exact weightedOperatorGramSquare
    (sourceSpinorKineticWeight M w) (sourceD (N := N))
    (-(spinorSquareNorm w : ℂ))
    (sourceSpinorKineticWeight_colorGram M w hgamma)

/-- The genuine CAR normal-order scalar factor 1/2 now gives exactly
the expected -||w||²/2 coefficient on the source second derivatives. -/
theorem sourceSpinorKineticDifferential_halfSquare {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (hgamma : M.gamma = originalGamma) :
    (1 / 2 : ℂ) • (∑ p : FermionLabel N,
      sourceSpinorKineticDifferential M w p *
      sourceSpinorKineticDifferential M w p) =
        (-(spinorSquareNorm w : ℂ) / 2) •
          sourceOriginalSecondDerivativeSum (N := N) := by
  rw [sourceSpinorKineticDifferential_square M w hgamma]
  rw [smul_smul]
  congr 1
  ring

#print axioms weightedOperatorGramSquare
#print axioms sourceSpinorKineticDifferential_square
#print axioms sourceSpinorKineticDifferential_halfSquare
#check @sourceSpinorKineticDifferential_square
#check @sourceSpinorKineticDifferential_halfSquare

end
end FCP.BFSSSU2PhysicalDomainL6G5C
