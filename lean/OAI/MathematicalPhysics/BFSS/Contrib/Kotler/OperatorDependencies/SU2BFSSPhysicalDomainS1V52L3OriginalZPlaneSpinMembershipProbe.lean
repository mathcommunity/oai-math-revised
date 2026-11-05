import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L2OriginalZPlaneLipschitzMembershipProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52S1Original48CliffordQuaternionStarUnitarityProbe

/-!
S1V52-L3 — STAGED, UNQUALIFIED original Z-plane quaternion
membership in the genuine pinned `spinGroup source48Quadratic`.

Precisely three independent prerequisite types:
* accepted S1 source Clifford star-unitarity,
* accepted S2 source Clifford evenness,
* L2 source exact genuine Lipschitz membership (qualify separately).

Do NOT treat ambient source Clifford units as automatically Spin.
The circle-coefficient norm is discharged from hcs, not postulated.
No global GaugeGroup lift, Y-plane Euler, source action or continuity
is claimed by this local original Z-plane lemma.
-/
set_option autoImplicit false
set_option maxHeartbeats 470000

namespace FCP.BFSSS1V52L3
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52S1
open FCP.BFSSS1V52S2
open FCP.BFSSS1V52L2

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- True original coordinate-unit norm certificate for an
honestly normalized Z-plane quaternion, with no extra hypothesis. -/
theorem sourceZPlaneQuaternion_norm (c s : ℝ)
    (hcs : c*c+s*s=1) :
    sourceQuaternionNormSq
      (⟨c,s,0,0⟩ : SourceQuaternionCoords) = 1 := by
  change c^2+s^2+0^2+0^2 = 1
  nlinarith [hcs]

/-- Fully qualified only when L2 is strictly verified: the literal
original 48-Clifford source Z-plane quaternion polynomial belongs
to pinned Mathlib's ACTUAL Spin group, not a fabricated model. -/
theorem sourceZPlaneQuaternion_mem_spin
    (α : RealSpinBlock) (c s : ℝ) (hcs : c*c+s*s=1) :
    sourceCliffordQuaternion α
      (⟨c,s,0,0⟩ : SourceQuaternionCoords) ∈ spinGroup Q := by
  have hp : sourceQuaternionNormSq
        (⟨c,s,0,0⟩ : SourceQuaternionCoords) = 1 :=
    sourceZPlaneQuaternion_norm c s hcs
  rw [spinGroup.mem_iff]
  constructor
  · rw [pinGroup.mem_iff]
    constructor
    · exact ⟨sourceCliffordQuaternionUnit α ⟨c,s,0,0⟩ hp,
          sourceZPlaneQuaternionUnit_mem_lipschitz α c s hcs hp,
          rfl⟩
    · rw [Unitary.mem_iff]
      exact ⟨sourceCliffordQuaternion_star_mul α ⟨c,s,0,0⟩ hp,
             sourceCliffordQuaternion_mul_star α ⟨c,s,0,0⟩ hp⟩
  · exact sourceCliffordQuaternion_mem_even α ⟨c,s,0,0⟩

/-- A concrete source-normalized original Z-plane Spin element;
this is local and does not yet define the full SU2 lift. -/
noncomputable def sourceZPlaneQuaternionSpin
    (α : RealSpinBlock) (c s : ℝ) (hcs : c*c+s*s=1) :
    spinGroup Q :=
  ⟨sourceCliffordQuaternion α ⟨c,s,0,0⟩,
   sourceZPlaneQuaternion_mem_spin α c s hcs⟩

theorem sourceZPlaneQuaternionSpin_coe
    (α : RealSpinBlock) (c s : ℝ) (hcs : c*c+s*s=1) :
    (sourceZPlaneQuaternionSpin α c s hcs : C) =
      sourceCliffordQuaternion α ⟨c,s,0,0⟩ := rfl

#print axioms sourceZPlaneQuaternion_norm
#print axioms sourceZPlaneQuaternion_mem_spin
#print axioms sourceZPlaneQuaternionSpin
#print axioms sourceZPlaneQuaternionSpin_coe
end
end FCP.BFSSS1V52L3
