import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG1APairedThetaProbe

/-!
# L6H5E8AD — source-exact opposite Clifford-nine orientation

The 2026 manuscript specifies an arbitrary symmetric real Cl(9) gamma
family but does not fix its central oriented gamma product. The concrete
signed-permutation source family has oriented product -I. We build the
*opposite* gamma orientation as a second genuine BFSS AlgebraData, not an
informal replacement inside untyped formulas. All 48 fermion generators,
color tensors, and source conventions are exactly preserved.

Replacing all nine gamma_i by -gamma_i reverses the odd Clifford volume,
while leaving gamma^{ij}, the SU2 colors and fermion field unchanged.
The parity intertwiner on actual TestFunction / L2 / closed physical
graphs is a distinct later obligation. No manuscript equivalence or
spectral conclusion is asserted here.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AD
noncomputable section

open OAI.BFSSQuantum

/-- Exact valid original BFSS AlgebraData with all nine spatial gamma
matrices reversed and no other source datum changed. -/
noncomputable def oppositeGamma {N : ℕ} (M : AlgebraData N) : AlgebraData N where
  color := M.color
  color_hermitian := M.color_hermitian
  color_traceless := M.color_traceless
  color_orthonormal := M.color_orthonormal
  color_spanning := M.color_spanning
  gamma := fun i => -M.gamma i
  gamma_symmetric := by
    intro i
    change (-M.gamma i).transpose = -M.gamma i
    simpa only [Matrix.transpose_neg] using congrArg Neg.neg (M.gamma_symmetric i)
  gamma_clifford := by
    intro i j
    change (-M.gamma i) * (-M.gamma j) +
      (-M.gamma j) * (-M.gamma i) =
        (if i = j then 2 else 0) • (1 : GammaMatrix)
    simpa only [neg_mul_neg] using M.gamma_clifford i j
  theta := M.theta
  theta_selfAdjoint := M.theta_selfAdjoint
  theta_CAR := M.theta_CAR
  theta_irreducible := M.theta_irreducible

/-- The opposite gamma system is pointwise negative to the source one. -/
theorem oppositeGamma_gamma {N : ℕ} (M : AlgebraData N)
    (i : SpaceIndex) : (oppositeGamma M).gamma i = -M.gamma i := rfl

/-- Same literal color structure constants, no orientation change in SU2. -/
theorem oppositeGamma_structureConstant {N : ℕ} (M : AlgebraData N)
    (A B C : ColorIndex N) :
    (oppositeGamma M).structureConstant A B C =
      M.structureConstant A B C := rfl

/-- Every gamma bivector is unchanged by flipping the nine vectors. -/
theorem oppositeGamma_gammaTwo {N : ℕ} (M : AlgebraData N)
    (i j : SpaceIndex) :
    (oppositeGamma M).gammaTwo i j = M.gammaTwo i j := by
  change (1 / 2 : ℝ) •
    ((-M.gamma i) * (-M.gamma j) -
     (-M.gamma j) * (-M.gamma i)) =
    (1 / 2 : ℝ) • (M.gamma i * M.gamma j - M.gamma j * M.gamma i)
  simp only [neg_mul_neg]

/-- Odd triple-gamma polarization reverses orientation. -/
theorem oppositeGamma_polarization {N : ℕ} (M : AlgebraData N) :
    (oppositeGamma M).polarization = -M.polarization := by
  change (-M.gamma 0) * (-M.gamma 1) * (-M.gamma 2) =
    -(M.gamma 0 * M.gamma 1 * M.gamma 2)
  -- The threefold orientation change is a noncommutative ring identity;
  -- avoid a brittle simp normalization of nested negations.
  noncomm_ring

/-- The 48 source fermion operators have not been relabeled or rescaled. -/
theorem oppositeGamma_theta {N : ℕ} (M : AlgebraData N)
    (α : SpinIndex) (A : ColorIndex N) :
    (oppositeGamma M).theta α A = M.theta α A := rfl

/-- Gamma opposition is an involution on the full concrete data. -/
theorem oppositeGamma_involutive {N : ℕ} (M : AlgebraData N) :
    oppositeGamma (oppositeGamma M) = M := by
  cases M
  simp [oppositeGamma]

#print axioms oppositeGamma
#print axioms oppositeGamma_gamma
#print axioms oppositeGamma_structureConstant
#print axioms oppositeGamma_gammaTwo
#print axioms oppositeGamma_polarization
#print axioms oppositeGamma_theta
#print axioms oppositeGamma_involutive

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AD
