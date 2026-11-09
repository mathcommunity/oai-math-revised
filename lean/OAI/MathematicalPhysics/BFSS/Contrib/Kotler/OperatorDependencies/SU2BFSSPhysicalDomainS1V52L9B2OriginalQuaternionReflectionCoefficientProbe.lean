import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9B1OriginalSameBlockQuaternionAxisReflectionProbe
import Mathlib.Tactic.Ring

/-!
S1V52-L9B2 — STAGED, UNQUALIFIED original +i source quaternion
coordinate identities for the three axis reflections.

This is only the elementary REAL quaternion multiplication step
needed to turn L9B1's same-block Clifford reflection into
the exact 3×3 adjoint coefficient matrix. It references the ORIGINAL
source positive-i quaternion product from strictly accepted B1.
No new source representation, trace formula, group action, Fock
intertwiner, or spectral theorem is introduced.

The preceding L9B1 candidate must be strictly qualified before this
module's own independent compilation/cache/axiom gate. Source-only
commit; NO CI triggered by this file.
-/
set_option autoImplicit false
set_option maxHeartbeats 280000

namespace FCP.BFSSS1V52L9B2
noncomputable section

open FCP.BFSSS1V52B1

/-- Axis e0, with the X-coordinate of the right quaternion reflected.
Its product has ZERO X component, so the eventual Clifford action
is vector-valued rather than carrying an unproved trivector part. -/
theorem originalQuat_axis0_reflect_compose
    (p : SourceQuaternionCoords) :
    sourceQuaternionCompose p ⟨p.a, p.b, p.c, -p.d⟩ =
      ⟨p.a^2-p.b^2-p.c^2+p.d^2,
       2*p.a*p.b-2*p.c*p.d,
       2*p.a*p.c+2*p.b*p.d,
       0⟩ := by
  cases p with
  | mk a b c d =>
    simp only [sourceQuaternionCompose]
    congr 1 <;> ring

/-- Axis e1: the right quaternion's Y-coordinate is reflected;
the quaternion product has ZERO Y component. -/
theorem originalQuat_axis1_reflect_compose
    (p : SourceQuaternionCoords) :
    sourceQuaternionCompose p ⟨p.a, p.b, -p.c, p.d⟩ =
      ⟨p.a^2-p.b^2+p.c^2-p.d^2,
       2*p.a*p.b+2*p.c*p.d,
       0,
       2*p.a*p.d-2*p.b*p.c⟩ := by
  cases p with
  | mk a b c d =>
    simp only [sourceQuaternionCompose]
    congr 1 <;> ring

/-- Axis e2: the right quaternion's Z-coordinate is reflected;
the quaternion product has ZERO Z component. -/
theorem originalQuat_axis2_reflect_compose
    (p : SourceQuaternionCoords) :
    sourceQuaternionCompose p ⟨p.a, -p.b, p.c, p.d⟩ =
      ⟨p.a^2+p.b^2-p.c^2-p.d^2,
       0,
       2*p.a*p.c-2*p.b*p.d,
       2*p.a*p.d+2*p.b*p.c⟩ := by
  cases p with
  | mk a b c d =>
    simp only [sourceQuaternionCompose]
    congr 1 <;> ring

#print axioms originalQuat_axis0_reflect_compose
#print axioms originalQuat_axis1_reflect_compose
#print axioms originalQuat_axis2_reflect_compose

end
end FCP.BFSSS1V52L9B2
