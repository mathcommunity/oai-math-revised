import OAI.MathematicalPhysics.BFSS.Core
import OAI.MathematicalPhysics.BFSS.GammaWords

/-!
# Source-defined BFSS Clifford spin-plane covariance

Original formalization contribution: **Evan T. Kotler**,
Foundational Convergence Program (independent research), 2026.

Copyright (c) 2026 Evan T. Kotler.
SPDX-License-Identifier: Apache-2.0

This formalization extends, but does not claim authorship of, the BFSS
model and Clifford algebra definitions originally provided by OpenAI.
It adapts the source-verified FCP S3A, S3B, S3L0 and S3L2 mathematical
identities to the upstream `OAI.BFSSQuantum.AlgebraData` interface.

The results concern the *actual source-defined* Cl(9) real gamma
matrices for any existing `AlgebraData N`. All proofs derive their
assumptions from its existing `gamma_clifford` and `gamma_symmetric`
fields; no substitute Clifford representation is introduced.

In particular these theorems do NOT assert a full Spin(9) group action,
gauge-invariant physical Hamiltonian symmetry, compact resolvent,
or positive BFSS eigenvalues.

Independent qualification of this adapted upstream module must be
recorded before claiming it is compiled. The FCP source versions
were previously kernel checked using Lean v4.34.1.
-/

namespace OAI.BFSSQuantum.AlgebraData

noncomputable section

variable {N : ℕ} (M : AlgebraData N)

/-- Source-normalized real spin generator for spatial plane `(i,j)`. -/
def sourceSpinPlaneGenerator (i j : SpaceIndex) : GammaMatrix :=
  (1 / 2 : ℝ) • M.gammaTwo i j

/-- Gamma two-forms built from the original symmetric gamma matrices
are skew under matrix transposition. -/
theorem sourceGammaTwo_skew (i j : SpaceIndex) :
    (M.gammaTwo i j).transpose = -(M.gammaTwo i j) := by
  have hs (k : SpaceIndex) : (M.gamma k).transpose = M.gamma k :=
    M.gamma_symmetric k
  change ((1 / 2 : ℝ) • (M.gamma i * M.gamma j -
    M.gamma j * M.gamma i)).transpose =
    -((1 / 2 : ℝ) • (M.gamma i * M.gamma j -
      M.gamma j * M.gamma i))
  simp only [Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_mul, hs]
  module

theorem sourceSpinPlaneGenerator_skew (i j : SpaceIndex) :
    (M.sourceSpinPlaneGenerator i j).transpose =
      -(M.sourceSpinPlaneGenerator i j) := by
  simp only [sourceSpinPlaneGenerator, Matrix.transpose_smul,
    M.sourceGammaTwo_skew, smul_neg]

/-- For distinct axes, the source Clifford gamma two-form equals the
ordered product, with precisely the normalization in `AlgebraData`. -/
theorem sourceGammaTwo_eq_mul (i j : SpaceIndex) (hij : i ≠ j) :
    M.gammaTwo i j = M.gamma i * M.gamma j := by
  change (1 / 2 : ℝ) • (M.gamma i * M.gamma j -
      M.gamma j * M.gamma i) = M.gamma i * M.gamma j
  have hanti := OAI.BFSSGamma.gamma_anti M.gamma M.gamma_clifford
    (Ne.symm hij)
  rw [hanti]
  module

/-- Infinitesimal Clifford spin action on the first plane axis. -/
theorem sourceSpinPlane_comm_gamma_i
    (i j : SpaceIndex) (hij : i ≠ j) :
    M.sourceSpinPlaneGenerator i j * M.gamma i -
      M.gamma i * M.sourceSpinPlaneGenerator i j = -(M.gamma j) := by
  have hi2 := OAI.BFSSGamma.gamma_sq M.gamma M.gamma_clifford i
  have hijanti := OAI.BFSSGamma.gamma_anti M.gamma M.gamma_clifford hij
  have hleft : (M.gamma i * M.gamma j) * M.gamma i = -(M.gamma j) := by
    calc
      _ = -(M.gamma j * M.gamma i) * M.gamma i := by rw [hijanti]
      _ = -(M.gamma j * (M.gamma i * M.gamma i)) := by
        simp only [neg_mul, Matrix.mul_assoc]
      _ = -(M.gamma j) := by rw [hi2, mul_one]
  have hright : M.gamma i * (M.gamma i * M.gamma j) = M.gamma j := by
    rw [← Matrix.mul_assoc, hi2, one_mul]
  rw [sourceSpinPlaneGenerator, M.sourceGammaTwo_eq_mul i j hij]
  rw [smul_mul_assoc, mul_smul_comm, hleft, hright]
  module

/-- Infinitesimal Clifford spin action on the second plane axis. -/
theorem sourceSpinPlane_comm_gamma_j
    (i j : SpaceIndex) (hij : i ≠ j) :
    M.sourceSpinPlaneGenerator i j * M.gamma j -
      M.gamma j * M.sourceSpinPlaneGenerator i j = M.gamma i := by
  have hj2 := OAI.BFSSGamma.gamma_sq M.gamma M.gamma_clifford j
  have hjianti := OAI.BFSSGamma.gamma_anti M.gamma M.gamma_clifford
    (Ne.symm hij)
  have hleft : (M.gamma i * M.gamma j) * M.gamma j = M.gamma i := by
    rw [Matrix.mul_assoc, hj2, mul_one]
  have hright : M.gamma j * (M.gamma i * M.gamma j) = -(M.gamma i) := by
    calc
      _ = (M.gamma j * M.gamma i) * M.gamma j := by rw [Matrix.mul_assoc]
      _ = -(M.gamma i * M.gamma j) * M.gamma j := by rw [hjianti]
      _ = -(M.gamma i) := by rw [neg_mul, Matrix.mul_assoc, hj2, mul_one]
  rw [sourceSpinPlaneGenerator, M.sourceGammaTwo_eq_mul i j hij]
  rw [smul_mul_assoc, mul_smul_comm, hleft, hright]
  module

/-- Infinitesimal Clifford action vanishes on transverse axes. -/
theorem sourceSpinPlane_comm_gamma_remaining
    (i j k : SpaceIndex) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    M.sourceSpinPlaneGenerator i j * M.gamma k -
      M.gamma k * M.sourceSpinPlaneGenerator i j = 0 := by
  have hikanti := OAI.BFSSGamma.gamma_anti M.gamma M.gamma_clifford hik
  have hjkanti := OAI.BFSSGamma.gamma_anti M.gamma M.gamma_clifford hjk
  have hcomm : (M.gamma i * M.gamma j) * M.gamma k =
      M.gamma k * (M.gamma i * M.gamma j) := by
    calc
      _ = M.gamma i * (M.gamma j * M.gamma k) := by rw [Matrix.mul_assoc]
      _ = M.gamma i * (-(M.gamma k * M.gamma j)) := by rw [hjkanti]
      _ = -(M.gamma i * M.gamma k) * M.gamma j := by
        simp only [mul_neg, neg_mul, Matrix.mul_assoc]
      _ = -(-(M.gamma k * M.gamma i)) * M.gamma j := by rw [hikanti]
      _ = M.gamma k * (M.gamma i * M.gamma j) := by
        simp only [neg_neg, Matrix.mul_assoc]
  rw [sourceSpinPlaneGenerator, M.sourceGammaTwo_eq_mul i j hij]
  rw [smul_mul_assoc, mul_smul_comm, hcomm, sub_self]

/-- The source-defined real gamma family transforms as a nine-vector
under each infinitesimal spatial plane. -/
theorem sourceSpinPlane_comm_gamma_all
    (i j k : SpaceIndex) (hij : i ≠ j) :
    M.sourceSpinPlaneGenerator i j * M.gamma k -
      M.gamma k * M.sourceSpinPlaneGenerator i j =
      if k = j then M.gamma i
      else if k = i then -(M.gamma j)
      else 0 := by
  by_cases hkj : k = j
  · subst k
    simpa [hij.symm] using M.sourceSpinPlane_comm_gamma_j i j hij
  by_cases hki : k = i
  · subst k
    simpa [hij] using M.sourceSpinPlane_comm_gamma_i i j hij
  · simpa [hkj, hki] using
      M.sourceSpinPlane_comm_gamma_remaining i j k hij
        (Ne.symm hki) (Ne.symm hkj)

/-- The source spatial gamma variation with the checked sign convention. -/
def sourceSpinGammaVariation (i j k : SpaceIndex) : GammaMatrix :=
  if k = j then M.gamma i
  else if k = i then -(M.gamma j)
  else 0

theorem sourceSpinGammaVariation_eq_comm
    (i j k : SpaceIndex) (hij : i ≠ j) :
    M.sourceSpinGammaVariation i j k =
      M.sourceSpinPlaneGenerator i j * M.gamma k -
      M.gamma k * M.sourceSpinPlaneGenerator i j := by
  exact (M.sourceSpinPlane_comm_gamma_all i j k hij).symm

/-- Exact source kinetic gamma coefficient, after the orbital variation;
the residual spinor index rotates by minus the original plane generator. -/
theorem sourceSpinKineticCoefficient
    (i j k : SpaceIndex) (hij : i ≠ j) :
    M.gamma k * (M.sourceSpinPlaneGenerator i j).transpose -
      M.sourceSpinGammaVariation i j k =
      -(M.sourceSpinPlaneGenerator i j * M.gamma k) := by
  rw [M.sourceSpinGammaVariation_eq_comm i j k hij,
    M.sourceSpinPlaneGenerator_skew]
  simp only [mul_neg]
  abel

#print axioms sourceGammaTwo_skew
#print axioms sourceSpinPlane_comm_gamma_i
#print axioms sourceSpinPlane_comm_gamma_j
#print axioms sourceSpinPlane_comm_gamma_remaining
#print axioms sourceSpinPlane_comm_gamma_all
#print axioms sourceSpinKineticCoefficient

end
end OAI.BFSSQuantum.AlgebraData
