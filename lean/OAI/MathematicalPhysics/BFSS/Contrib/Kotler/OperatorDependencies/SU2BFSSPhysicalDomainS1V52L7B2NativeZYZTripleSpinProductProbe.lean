import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L7B1NativeZYCoordinateSpinProductProbe

/-!
S1V52-L7B2 — STAGED, NOT STRICTLY QUALIFIED.

The actual original GaugeGroup 2 ZYZ triple product maps to genuine
original source Spin(48) when all THREE native source quaternion
coordinates are exact normalized Z/Y/Z circles. Reuses L7B1's
source-native ZY multiplication and independently accepted L3
source Z membership, WITHOUT assuming Euler factorization or
suppressing the native coordinate hypotheses.

After L7B1 and this gate qualify, original S1V23/L6H5E8R/T/Y
curve-to-quaternion and exact source Euler identities can be
transported into genuine Spin(48) using the historical source
closure. That last transport is not inferred here.

Original positive-i Pauli convention, t*pauliScale and actual
source48Quadratic; no surrogate GaugeGroup, no physical/spectral
claim and no global Spin hom at this stage.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
namespace FCP.BFSSS1V52L7B2
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52C2D
open FCP.BFSSS1V52L7B1

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Genuine native SU(2) original ZYZ-product source Clifford
Spin membership, WITHOUT silently assuming the still-separate
historical positive-i curve and Euler identities. -/
theorem originalNativeZYZProduct_mem_spin
    (α : RealSpinBlock) (g h k : GaugeGroup 2)
    (c s u v w x : ℝ)
    (hg : originalNativeQuaternionCoords g =
      (⟨c,s,0,0⟩ : SourceQuaternionCoords))
    (hh : originalNativeQuaternionCoords h =
      (⟨u,0,v,0⟩ : SourceQuaternionCoords))
    (hk : originalNativeQuaternionCoords k =
      (⟨w,x,0,0⟩ : SourceQuaternionCoords))
    (hcs : c*c+s*s=1) (huv : u*u+v*v=1)
    (hwx : w*w+x*x=1) :
    sourceCliffordQuaternion α
      (originalNativeQuaternionCoords (g*h*k)) ∈ spinGroup Q := by
  rw [originalNativeQuaternionCoords_mul]
  rw [sourceCliffordQuaternion_compose]
  exact mul_mem
    (originalNativeZYProduct_mem_spin α g h c s u v hg hh hcs huv)
    (originalNativeZCoordinate_mem_spin α k w x hk hwx)

/-- Actual native SU2 membership, rather than an assumed length-one
premise, automatically normalizes the original positive-i Z
quaternion coordinate circle. -/
theorem originalNativeZCoordinate_norm
    (g : GaugeGroup 2) (c s : ℝ)
    (hg : originalNativeQuaternionCoords g =
      (⟨c,s,0,0⟩ : SourceQuaternionCoords)) :
    c*c+s*s=1 := by
  have hn : sourceQuaternionNormSq
      (⟨c,s,0,0⟩ : SourceQuaternionCoords) = 1 := by
    simpa only [hg] using (originalNativeQuaternion_norm_one g)
  change c^2+s^2+0^2+0^2=1 at hn
  nlinarith [hn]

/-- The native SU2 unitary group automatically normalizes the
original positive-sine Y quaternion coordinate circle. -/
theorem originalNativeYCoordinate_norm
    (h : GaugeGroup 2) (u v : ℝ)
    (hh : originalNativeQuaternionCoords h =
      (⟨u,0,v,0⟩ : SourceQuaternionCoords)) :
    u*u+v*v=1 := by
  have hn : sourceQuaternionNormSq
      (⟨u,0,v,0⟩ : SourceQuaternionCoords) = 1 := by
    simpa only [hh] using (originalNativeQuaternion_norm_one h)
  change u^2+0^2+v^2+0^2=1 at hn
  nlinarith [hn]

/-- No separate quaternion normalization hypotheses are needed
for actual native SU2 ZY products; unit norm is inherited
from the original pinned GaugeGroup 2 membership. -/
theorem originalNativeZYProduct_mem_spin_auto
    (α : RealSpinBlock) (g h : GaugeGroup 2)
    (c s u v : ℝ)
    (hg : originalNativeQuaternionCoords g =
      (⟨c,s,0,0⟩ : SourceQuaternionCoords))
    (hh : originalNativeQuaternionCoords h =
      (⟨u,0,v,0⟩ : SourceQuaternionCoords)) :
    sourceCliffordQuaternion α
      (originalNativeQuaternionCoords (g*h)) ∈ spinGroup Q := by
  exact originalNativeZYProduct_mem_spin α g h c s u v hg hh
    (originalNativeZCoordinate_norm g c s hg)
    (originalNativeYCoordinate_norm h u v hh)

/-- Unconditional normalization for an actual original native
ZYZ-coordinate product. Still does not assert that every native
element HAS the original historical Euler factorization. -/
theorem originalNativeZYZProduct_mem_spin_auto
    (α : RealSpinBlock) (g h k : GaugeGroup 2)
    (c s u v w x : ℝ)
    (hg : originalNativeQuaternionCoords g =
      (⟨c,s,0,0⟩ : SourceQuaternionCoords))
    (hh : originalNativeQuaternionCoords h =
      (⟨u,0,v,0⟩ : SourceQuaternionCoords))
    (hk : originalNativeQuaternionCoords k =
      (⟨w,x,0,0⟩ : SourceQuaternionCoords)) :
    sourceCliffordQuaternion α
      (originalNativeQuaternionCoords (g*h*k)) ∈ spinGroup Q := by
  exact originalNativeZYZProduct_mem_spin
    α g h k c s u v w x hg hh hk
    (originalNativeZCoordinate_norm g c s hg)
    (originalNativeYCoordinate_norm h u v hh)
    (originalNativeZCoordinate_norm k w x hk)

#print axioms originalNativeZYZProduct_mem_spin
#print axioms originalNativeZCoordinate_norm
#print axioms originalNativeYCoordinate_norm
#print axioms originalNativeZYProduct_mem_spin_auto
#print axioms originalNativeZYZProduct_mem_spin_auto
end
end FCP.BFSSS1V52L7B2
