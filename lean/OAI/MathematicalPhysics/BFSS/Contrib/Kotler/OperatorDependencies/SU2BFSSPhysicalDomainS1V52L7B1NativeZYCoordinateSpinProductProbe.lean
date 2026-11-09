import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L6OriginalYPlaneSpinMembershipProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L3OriginalZPlaneSpinMembershipProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52C2EOriginalNativeGaugeCliffordUnitHomProbe

/-!
S1V52-L7B1 — ORIGINAL native GaugeGroup 2, original positive-i
quaternion coordinates and original actual source48 Spin.

Proves genuine Spin membership for any actual native SU(2) group
element with Z- or Y-circle quaternion coordinates, and for their
native group product. The normalized coordinates are EXPLICIT
hypotheses, not substituted historical source curve identities.
Uses accepted C2D exact native quaternion multiplication and
B2 exact source Clifford quaternion multiplication; importantly
does not assume even unitary implies Lipschitz membership.

All group and Clifford types remain pinned actual original
GaugeGroup 2 and CliffordAlgebra source48Quadratic. Does NOT
assert Euler factorization, membership for all native elements,
a continuous group hom, or original BFSS spectrum.
-/
set_option autoImplicit false
set_option maxHeartbeats 430000

namespace FCP.BFSSS1V52L7B1
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52C2D
open FCP.BFSSS1V52L3
open FCP.BFSSS1V52L6

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Genuine original native SU(2) Z-circle coordinate implies
the exact original block Clifford element belongs to real Spin48. -/
theorem originalNativeZCoordinate_mem_spin
    (α : RealSpinBlock) (g : GaugeGroup 2) (c s : ℝ)
    (hcoords : originalNativeQuaternionCoords g =
      (⟨c,s,0,0⟩ : SourceQuaternionCoords))
    (hcs : c*c+s*s=1) :
    sourceCliffordQuaternion α (originalNativeQuaternionCoords g) ∈
      spinGroup Q := by
  rw [hcoords]
  exact sourceZPlaneQuaternion_mem_spin α c s hcs

/-- Independent Y-circle original native source Spin certificate,
with the original positive real upper-right quaternion sine. -/
theorem originalNativeYCoordinate_mem_spin
    (α : RealSpinBlock) (g : GaugeGroup 2) (c s : ℝ)
    (hcoords : originalNativeQuaternionCoords g =
      (⟨c,0,s,0⟩ : SourceQuaternionCoords))
    (hcs : c*c+s*s=1) :
    sourceCliffordQuaternion α (originalNativeQuaternionCoords g) ∈
      spinGroup Q := by
  rw [hcoords]
  exact sourceYPlaneQuaternion_mem_spin α c s hcs

/-- The product in the ACTUAL original GaugeGroup 2 is carried
to a product inside ACTUAL original source Spin48. Unlike a
generic even/unitary argument, this uses exact accepted
native quaternion multiplication and proven Spin closure. -/
theorem originalNativeZYProduct_mem_spin
    (α : RealSpinBlock) (g h : GaugeGroup 2)
    (c s u v : ℝ)
    (hg : originalNativeQuaternionCoords g =
      (⟨c,s,0,0⟩ : SourceQuaternionCoords))
    (hh : originalNativeQuaternionCoords h =
      (⟨u,0,v,0⟩ : SourceQuaternionCoords))
    (hcs : c*c+s*s=1) (huv : u*u+v*v=1) :
    sourceCliffordQuaternion α
      (originalNativeQuaternionCoords (g*h)) ∈ spinGroup Q := by
  rw [originalNativeQuaternionCoords_mul]
  rw [sourceCliffordQuaternion_compose]
  exact mul_mem
    (originalNativeZCoordinate_mem_spin α g c s hg hcs)
    (originalNativeYCoordinate_mem_spin α h u v hh huv)

#print axioms originalNativeZCoordinate_mem_spin
#print axioms originalNativeYCoordinate_mem_spin
#print axioms originalNativeZYProduct_mem_spin
end
end FCP.BFSSS1V52L7B1
