import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5QOriginalDiagonalMixedCommutatorProbe
import Mathlib.Tactic.Module

/-!
L6G5R: the exact original gamma/bivector commutator with its
SO(9) Clifford sign and both spatial Kronecker coefficients.

The raw noncommutative identity is proved abstractly, and then the
actual source AlgebraData gamma Clifford relations discharge every
premise. This is a source gamma identity, not yet the contracted row
spinor identity, orbital Gauss, fermionic Gauss, or spectral bridge.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5R
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData

/-- The Clifford bivector commutator is algebraic in only two
anticommutators; no triple-index enumeration is needed. The
anticommutators have genuinely CENTRAL real scalars. -/
private theorem bivector_commutator_of_anticommutators
    {R : Type*} [Ring R] [Algebra ℝ R]
    (A B C : R) (s t : ℝ)
    (hAB : A * B + B * A = s • (1 : R))
    (hAC : A * C + C * A = t • (1 : R)) :
    A * ((1 / 2 : ℝ) • (B * C - C * B)) -
      ((1 / 2 : ℝ) • (B * C - C * B)) * A =
        s • C - t • B := by
  have hcore :
      A * (B * C - C * B) - (B * C - C * B) * A =
        ((A * B + B * A) * C + C * (A * B + B * A)) -
          ((A * C + C * A) * B + B * (A * C + C * A)) := by
    noncomm_ring
  calc
    _ = (1 / 2 : ℝ) •
          (A * (B * C - C * B) -
            (B * C - C * B) * A) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    _ = (1 / 2 : ℝ) •
          (((A * B + B * A) * C + C * (A * B + B * A)) -
            ((A * C + C * A) * B + B * (A * C + C * A))) :=
      congrArg (fun x : R => (1 / 2 : ℝ) • x) hcore
    _ = s • C - t • B := by
      rw [hAB, hAC]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module

/-- The source gammaTwo is skew-transpose, relying only on the
source gamma-symmetry fields and the unchanged upstream definition. -/
theorem sourceGammaTwo_skew_transpose {N : ℕ}
    (M : AlgebraData N) (j k : SpaceIndex) :
    (M.gammaTwo j k).transpose = -M.gammaTwo j k := by
  change (OAI.BFSSGamma.gammaTwo M.gamma j k).transpose =
    -OAI.BFSSGamma.gammaTwo M.gamma j k
  simp only [OAI.BFSSGamma.gammaTwo, Matrix.transpose_smul,
    Matrix.transpose_sub, Matrix.transpose_mul,
    (M.gamma_symmetric j).eq, (M.gamma_symmetric k).eq,
    ← smul_neg, neg_sub]

/-- The EXACT original source Clifford commutator, with no added
spin, color, gauge, or representation premises. The transpose sign
is essential in the next row-spinor contraction. -/
theorem sourceGamma_bivector_commutator {N : ℕ}
    (M : AlgebraData N) (i j k : SpaceIndex) :
    M.gamma i * M.gammaTwo j k -
      M.gammaTwo j k * M.gamma i =
        (if i = j then (2 : ℝ) else 0) • M.gamma k -
          (if i = k then (2 : ℝ) else 0) • M.gamma j := by
  change M.gamma i *
      ((1 / 2 : ℝ) • (M.gamma j * M.gamma k - M.gamma k * M.gamma j)) -
        ((1 / 2 : ℝ) • (M.gamma j * M.gamma k - M.gamma k * M.gamma j)) *
          M.gamma i = _
  have hcliffordReal (u v : SpaceIndex) :
      M.gamma u * M.gamma v + M.gamma v * M.gamma u =
        (if u = v then (2 : ℝ) else 0) • (1 : GammaMatrix) := by
    by_cases huv : u = v
    · simpa only [if_pos huv, two_smul] using (M.gamma_clifford u v)
    · simpa only [if_neg huv, zero_smul] using (M.gamma_clifford u v)
  exact bivector_commutator_of_anticommutators
    (M.gamma i) (M.gamma j) (M.gamma k)
    (if i = j then 2 else 0) (if i = k then 2 else 0)
    (hcliffordReal i j) (hcliffordReal i k)

#print axioms bivector_commutator_of_anticommutators
#print axioms sourceGammaTwo_skew_transpose
#print axioms sourceGamma_bivector_commutator
#check @sourceGamma_bivector_commutator
end
end FCP.BFSSSU2PhysicalDomainL6G5R
