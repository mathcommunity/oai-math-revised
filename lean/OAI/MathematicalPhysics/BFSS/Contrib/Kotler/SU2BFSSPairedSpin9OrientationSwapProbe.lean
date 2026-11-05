import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9PlaneGeneratorProbe

/-!
K1D18V8D — original paired-Fock Spin(9) plane orientation swap.

This is an independent small theorem about the actual source 48-real
paired-label matrix, not an assumption that the color-major matrix is
identical. It reuses the accepted V8A generator and the exact original
gamma Clifford identity. For r ≠ s, K(s,r) = -K(r,s).
No Lie-group lift, global Fock action, or physical spectrum follows.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSGamma9
open scoped Kronecker

private theorem gamma_swap_order (r s : SpaceIndex) (hrs : r ≠ s) :
    gamma s * gamma r = -(gamma r * gamma s) := by
  have h : gamma r * gamma s + gamma s * gamma r = 0 := by
    simpa [hrs] using (FCP.BFSSGamma9.gamma_clifford r s)
  calc
    gamma s * gamma r =
        (gamma r * gamma s + gamma s * gamma r) - gamma r * gamma s := by
      abel
    _ = -(gamma r * gamma s) := by rw [h]; simp

private theorem plane16_swap_order (r s : SpaceIndex) (hrs : r ≠ s) :
    plane16 s r = -(plane16 r s) := by
  calc
    plane16 s r = -(gamma s * gamma r) := rfl
    _ = -(-(gamma r * gamma s)) := by
      rw [gamma_swap_order r s hrs]
    _ = -(plane16 r s) := by simp [plane16]

private theorem blockPlane_swap_order (r s : SpaceIndex) (hrs : r ≠ s) :
    ((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 s r) =
      -((1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 r s) := by
  rw [plane16_swap_order r s hrs]
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [Matrix.kronecker_apply, Matrix.neg_apply, mul_neg]

/-- Exact sign of an oriented gamma plane generator transported to the
original paired Fock 48-label basis, with r and s distinct. -/
theorem originalPairedPlane_swap_order (r s : SpaceIndex) (hrs : r ≠ s) :
    originalPairedPlane s r = -(originalPairedPlane r s) := by
  let E := Matrix.reindexRingEquiv ℝ pairedColorSpinEquiv
  let B (a b : SpaceIndex) :
      Matrix (ColorIndex 2 × SpinIndex) (ColorIndex 2 × SpinIndex) ℝ :=
    (1 : Matrix (ColorIndex 2) (ColorIndex 2) ℝ) ⊗ₖ plane16 a b
  have h : B s r = -(B r s) := blockPlane_swap_order r s hrs
  change E (B s r) = -(E (B r s))
  calc
    E (B s r) = E (-(B r s)) := congrArg E h
    _ = -(E (B r s)) := by rw [map_neg]

#print axioms originalPairedPlane_swap_order

end
end FCP.BFSSPairedSpin9Plane
