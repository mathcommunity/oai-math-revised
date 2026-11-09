import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L5OriginalYPlaneLipschitzMembershipProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52S1Original48CliffordQuaternionStarUnitarityProbe

/-!
S1V52-L6 — STAGED, UNQUALIFIED original Y-plane quaternion
membership in the genuine pinned `spinGroup source48Quadratic`.

Precisely three independent prerequisite types:
* accepted S1 source Clifford star-unitarity,
* accepted S2 source Clifford evenness,
* L5 source exact genuine Y Lipschitz membership (qualify separately).

Do NOT treat ambient source Clifford units as automatically Spin.
The circle-coefficient norm is discharged from hcs, not postulated.
No global GaugeGroup lift, exact Euler transport, source action or continuity
is claimed by this local original Y-plane lemma.
-/
set_option autoImplicit false
set_option maxHeartbeats 470000

namespace FCP.BFSSS1V52L6
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52S1
open FCP.BFSSS1V52S2
open FCP.BFSSS1V52L5

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- True original coordinate-unit norm certificate for an
honestly normalized Y-plane quaternion, with no extra hypothesis. -/
theorem sourceYPlaneQuaternion_norm (c s : ℝ)
    (hcs : c*c+s*s=1) :
    sourceQuaternionNormSq
      (⟨c,0,s,0⟩ : SourceQuaternionCoords) = 1 := by
  change c^2+0^2+s^2+0^2 = 1
  nlinarith [hcs]

/-- Fully qualified only when L2 is strictly verified: the literal
original 48-Clifford source Y-plane quaternion polynomial belongs
to pinned Mathlib's ACTUAL Spin group, not a fabricated model. -/
theorem sourceYPlaneQuaternion_mem_spin
    (α : RealSpinBlock) (c s : ℝ) (hcs : c*c+s*s=1) :
    sourceCliffordQuaternion α
      (⟨c,0,s,0⟩ : SourceQuaternionCoords) ∈ spinGroup Q := by
  have hp : sourceQuaternionNormSq
        (⟨c,0,s,0⟩ : SourceQuaternionCoords) = 1 :=
    sourceYPlaneQuaternion_norm c s hcs
  rw [spinGroup.mem_iff]
  constructor
  · rw [pinGroup.mem_iff]
    constructor
    · exact ⟨sourceCliffordQuaternionUnit α ⟨c,0,s,0⟩ hp,
          sourceYPlaneQuaternionUnit_mem_lipschitz α c s hcs hp,
          rfl⟩
    · rw [Unitary.mem_iff]
      exact ⟨sourceCliffordQuaternion_star_mul α ⟨c,0,s,0⟩ hp,
             sourceCliffordQuaternion_mul_star α ⟨c,0,s,0⟩ hp⟩
  · exact sourceCliffordQuaternion_mem_even α ⟨c,0,s,0⟩

/-- A concrete source-normalized original Y-plane Spin element;
this is local and does not yet define the full SU2 lift. -/
noncomputable def sourceYPlaneQuaternionSpin
    (α : RealSpinBlock) (c s : ℝ) (hcs : c*c+s*s=1) :
    spinGroup Q :=
  ⟨sourceCliffordQuaternion α ⟨c,0,s,0⟩,
   sourceYPlaneQuaternion_mem_spin α c s hcs⟩

theorem sourceYPlaneQuaternionSpin_coe
    (α : RealSpinBlock) (c s : ℝ) (hcs : c*c+s*s=1) :
    (sourceYPlaneQuaternionSpin α c s hcs : C) =
      sourceCliffordQuaternion α ⟨c,0,s,0⟩ := rfl

#print axioms sourceYPlaneQuaternion_norm
#print axioms sourceYPlaneQuaternion_mem_spin
#print axioms sourceYPlaneQuaternionSpin
#print axioms sourceYPlaneQuaternionSpin_coe
end
end FCP.BFSSS1V52L6
