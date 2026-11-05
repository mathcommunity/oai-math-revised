import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52B3Original48CliffordQuaternionUnitNormProbe
import OAI.MathematicalPhysics.BFSS.Core
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
S1V52-C1: actual native original GaugeGroup 2 (definitionally
Matrix.specialUnitaryGroup (Fin 2) ℂ in the immutable upstream
OAI.MathematicalPhysics.BFSS.Core), into the EXACT positive-i
quaternion coordinates established by S1V52B1.

This is a coordinate extraction and unit-norm BRIDGE, not a
replacement SU2 group. Its FCP source imports the genuine upstream
BFSS Core; strict CI must compile the source Core file from the
pinned upstream math checkout, never a copied or invented module.

The next independent theorem (C2) will prove whole-matrix
reconstruction and coordinates of a native product, using qualified
L6H5E8P/Q geometric facts or their exact original-source proofs.
The group-to-Spin lift is not implied by this step.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSS1V52C1
noncomputable section

open OAI.BFSSQuantum
open Matrix
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B3

/-- The native original source SU2 first-row quaternion coordinate.
The source type is exactly OAI.BFSSQuantum.GaugeGroup 2. -/
def originalNativeQuaternionCoords (g : GaugeGroup 2) :
    SourceQuaternionCoords :=
  ⟨((g : ColorMatrix 2) 0 0).re,
   ((g : ColorMatrix 2) 0 0).im,
   ((g : ColorMatrix 2) 0 1).re,
   ((g : ColorMatrix 2) 0 1).im⟩

/-- Proof that these are coordinates of the original (0,0) entry. -/
theorem originalNativeQuaternion_u (g : GaugeGroup 2) :
    (originalNativeQuaternionCoords g).a +
      (originalNativeQuaternionCoords g).b * Complex.I =
        (g : ColorMatrix 2) 0 0 := by
  exact Complex.re_add_im ((g : ColorMatrix 2) 0 0)

/-- Proof that these are coordinates of the original (0,1) entry. -/
theorem originalNativeQuaternion_v (g : GaugeGroup 2) :
    (originalNativeQuaternionCoords g).c +
      (originalNativeQuaternionCoords g).d * Complex.I =
        (g : ColorMatrix 2) 0 1 := by
  exact Complex.re_add_im ((g : ColorMatrix 2) 0 1)

/-- Every actual, native original SU2 source gauge element has exactly
unit quaternion-coordinate norm. Not assumed; derived from source
unitarity and the literal 2x2 Hermitian adjoint. -/
theorem originalNativeQuaternion_norm_one (g : GaugeGroup 2) :
    sourceQuaternionNormSq (originalNativeQuaternionCoords g) = 1 := by
  let A : ColorMatrix 2 := g
  have hu : A * Aᴴ = (1 : ColorMatrix 2) := by
    have hm : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := g.property.1
    simpa only [Matrix.star_eq_conjTranspose] using hm.2
  have h00 :
      A 0 0 * star (A 0 0) + A 0 1 * star (A 0 1) = (1 : ℂ) := by
    have h := congrArg (fun M : ColorMatrix 2 => M 0 0) hu
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hnorm :
      Complex.normSq (A 0 0) + Complex.normSq (A 0 1) = 1 := by
    have hcast :
        ((Complex.normSq (A 0 0) : ℝ) : ℂ) +
          ((Complex.normSq (A 0 1) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_conj_mul_self]
      change star (A 0 0) * A 0 0 +
        star (A 0 1) * A 0 1 = 1
      calc
        star (A 0 0) * A 0 0 + star (A 0 1) * A 0 1 =
            A 0 0 * star (A 0 0) + A 0 1 * star (A 0 1) := by ring
        _ = 1 := h00
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using hcast
  rw [Complex.normSq_apply, Complex.normSq_apply] at hnorm
  dsimp [sourceQuaternionNormSq, originalNativeQuaternionCoords]
  nlinarith [hnorm]

#print axioms originalNativeQuaternion_u
#print axioms originalNativeQuaternion_v
#print axioms originalNativeQuaternion_norm_one

end
end FCP.BFSSS1V52C1
