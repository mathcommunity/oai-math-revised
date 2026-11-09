import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9PlaneGeneratorProbe

/-!
K1D18V8B — an original paired-label Spin(9) Lie-bracket specialization.

This candidate proves only the adjacent-plane bracket for THREE PAIRWISE
DISTINCT original spatial indices on the true Source48Label = Fin24 × Fin2.
It uses the accepted V8A originalPairedPlane, which transports the literal
gamma products by the original pairedLabelEquiv. The doubled plane generators
satisfy [K(r,s), K(s,t)] = -2 K(r,t), with the exact sign and factor two.

Not a general so(9) Lie representation, group integration, global Fock action,
or Hamiltonian / spectral theorem. No proof limits are changed.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSGamma9
open scoped Kronecker

/-- Original gamma-square law, obtained from the actual nine-gamma Clifford
identity, without changing the accepted V8A source module. -/
private theorem gamma_one_sq (r : SpaceIndex) :
    gamma r * gamma r = (1 : GammaMatrix) := by
  have h : gamma r * gamma r + gamma r * gamma r =
      (1 : GammaMatrix) + (1 : GammaMatrix) := by
    simpa only [eq_self, ite_true, two_smul] using
      (FCP.BFSSGamma9.gamma_clifford r r)
  ext i j
  have hij := congrArg (fun M : GammaMatrix => M i j) h
  simp only [Matrix.add_apply] at hij
  linarith

private theorem gamma_anticommute (r s : SpaceIndex) (hrs : r ≠ s) :
    gamma s * gamma r = -(gamma r * gamma s) := by
  have h : gamma r * gamma s + gamma s * gamma r = 0 := by
    simpa [hrs] using (FCP.BFSSGamma9.gamma_clifford r s)
  calc
    gamma s * gamma r =
        (gamma r * gamma s + gamma s * gamma r) - gamma r * gamma s := by
      abel
    _ = -(gamma r * gamma s) := by rw [h]; simp

private theorem plane16_adjacent_forward (r s t : SpaceIndex) :
    plane16 r s * plane16 s t = -(plane16 r t) := by
  calc
    plane16 r s * plane16 s t =
        (gamma r * gamma s) * (gamma s * gamma t) := by
      simp only [plane16, neg_mul_neg]
    _ = gamma r * (gamma s * gamma s) * gamma t := by
      simp only [mul_assoc]
    _ = gamma r * gamma t := by rw [gamma_one_sq s]; simp
    _ = -(plane16 r t) := by simp [plane16]

private theorem plane16_adjacent_reverse (r s t : SpaceIndex)
    (hrs : r ≠ s) (hst : s ≠ t) (hrt : r ≠ t) :
    plane16 s t * plane16 r s = plane16 r t := by
  calc
    plane16 s t * plane16 r s =
        (gamma s * gamma t) * (gamma r * gamma s) := by
      simp only [plane16, neg_mul_neg]
    _ = gamma s * (gamma t * gamma r) * gamma s := by
      simp only [mul_assoc]
    _ = gamma s * (-(gamma r * gamma t)) * gamma s := by
      rw [gamma_anticommute r t hrt]
    _ = -(gamma s * gamma r * gamma t * gamma s) := by
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = -((-(gamma r * gamma s)) * gamma t * gamma s) := by
      rw [gamma_anticommute r s hrs]
    _ = gamma r * gamma s * gamma t * gamma s := by
      simp only [neg_mul, neg_neg]
    _ = gamma r * (gamma s * gamma t) * gamma s := by
      simp only [mul_assoc]
    _ = gamma r * (-(gamma t * gamma s)) * gamma s := by
      rw [gamma_anticommute t s (Ne.symm hst)]
    _ = -((gamma r * gamma t) * (gamma s * gamma s)) := by
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = -(gamma r * gamma t) := by
      rw [gamma_one_sq s, mul_one]
    _ = plane16 r t := by simp [plane16]

private theorem plane16_adjacent_bracket (r s t : SpaceIndex)
    (hrs : r ≠ s) (hst : s ≠ t) (hrt : r ≠ t) :
    plane16 r s * plane16 s t - plane16 s t * plane16 r s =
      -(plane16 r t + plane16 r t) := by
  rw [plane16_adjacent_forward r s t,
    plane16_adjacent_reverse r s t hrs hst hrt]
  abel

private theorem blockPlane_mul (r s u v : SpaceIndex) :
    ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s) *
        ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 u v) =
      ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ
        (plane16 r s * plane16 u v)) := by
  simpa only [one_mul] using
    (Matrix.mul_kronecker_mul
      (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ)
      (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ)
      (plane16 r s) (plane16 u v)).symm

/-- The first nontrivial Lie-bracket relation on the actual original
paired-Fock 48-real generators. This is the doubled-generator normalization:
the RHS is minus two times the (r,t) generator. -/
theorem originalPairedPlane_adjacent_bracket
    (r s t : SpaceIndex) (hrs : r ≠ s) (hst : s ≠ t) (hrt : r ≠ t) :
    originalPairedPlane r s * originalPairedPlane s t -
        originalPairedPlane s t * originalPairedPlane r s =
      -(originalPairedPlane r t + originalPairedPlane r t) := by
  let E := Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv
  let B (a b : SpaceIndex) :
      Matrix (ColorIndex 2 × SpinIndex) (ColorIndex 2 × SpinIndex) ℝ :=
    ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 a b)
  change E (B r s) * E (B s t) - E (B s t) * E (B r s) =
      -(E (B r t) + E (B r t))
  calc
    E (B r s) * E (B s t) - E (B s t) * E (B r s) =
        E (B r s * B s t - B s t * B r s) := by
      simp only [map_sub, map_mul]
    _ = E (-(B r t + B r t)) := by
      apply congrArg E
      dsimp [B]
      rw [blockPlane_mul r s s t, blockPlane_mul s t r s]
      calc
        ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ
            (plane16 r s * plane16 s t)) -
            ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ
              (plane16 s t * plane16 r s)) =
          ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ
            (plane16 r s * plane16 s t - plane16 s t * plane16 r s)) := by
          ext ⟨a,i⟩ ⟨b,j⟩
          simp only [Matrix.kronecker_apply, Matrix.sub_apply, mul_sub]
        _ = ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ
            (-(plane16 r t + plane16 r t))) := by
          rw [plane16_adjacent_bracket r s t hrs hst hrt]
        _ = -(((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ
                plane16 r t) +
              ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ
                plane16 r t)) := by
          ext ⟨a,i⟩ ⟨b,j⟩
          simp only [Matrix.kronecker_apply, Matrix.add_apply,
            Matrix.neg_apply, mul_add, mul_neg]
    _ = -(E (B r t) + E (B r t)) := by
      simp only [map_neg, map_add]

#print axioms originalPairedPlane_adjacent_bracket

end
end FCP.BFSSPairedSpin9Plane
