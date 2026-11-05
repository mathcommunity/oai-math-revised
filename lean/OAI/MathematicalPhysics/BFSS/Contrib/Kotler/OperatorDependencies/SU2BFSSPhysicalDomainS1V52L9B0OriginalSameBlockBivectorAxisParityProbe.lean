import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9AOriginalNativeCrossBlockMajoranaCliffordFixationProbe

/-!
S1V52-L9B0 — SAME-BLOCK axis/bivector parity table, source-faithful
and deliberately separated from the pending full quaternion adjoint action.

For the ACTUAL source Q on Fin 24 × Fin 2 real Majorana labels, the
three original color axes anticommute with precisely the two incident
bivectors and commute with the disjoint bivector. The oriented bivectors
are EXACTLY accepted S1V52A: Z=e0*e1, Y=e2*e0, X=e1*e2.

These nine relations are the algebraic interface needed to move the
actual source Clifford star-conjugate quaternion across a generator.
They are NOT the conjugation theorem, nor original adjointColorMatrix
equality, full sixteen-block action, continuity or BFSS spectral result.

Staged candidate only. Count ZERO roots until strict source-pinned
CI compiles all nine statements and the permitted-axiom audit passes.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52L9B0
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev E (α : RealSpinBlock) (i : Fin 3) : C :=
  CliffordAlgebra.ι Q (sourceBlockColorAxis α i)

/-- Generic algebraic relation: the first generator anticommutes
with its own bivector when the two generators anticommute. -/
private theorem bivector_first_anticomm (u v : C)
    (hvu : v * u = -(u * v)) :
    u * (u * v) = -((u * v) * u) := by
  have h : (u * v) * u = -(u * (u * v)) := by
    calc
      (u * v) * u = u * (v * u) := by simp only [mul_assoc]
      _ = u * (-(u * v)) := by rw [hvu]
      _ = -(u * (u * v)) := by rw [mul_neg]
  rw [h]
  simp only [neg_neg]

/-- Generic algebraic relation for the second generator. -/
private theorem bivector_second_anticomm (u v : C)
    (hvu : v * u = -(u * v)) :
    v * (u * v) = -((u * v) * v) := by
  calc
    v * (u * v) = (v * u) * v := by simp only [mul_assoc]
    _ = (-(u * v)) * v := by rw [hvu]
    _ = -((u * v) * v) := by rw [neg_mul]

/-- Moving through two other anticommuting generators incurs two
sign changes, so a nonincident source bivector commutes. -/
private theorem bivector_third_comm (w u v : C)
    (hwu : w * u = -(u * w))
    (hwv : w * v = -(v * w)) :
    w * (u * v) = (u * v) * w := by
  calc
    w * (u * v) = (w * u) * v := by simp only [mul_assoc]
    _ = (-(u * w)) * v := by rw [hwu]
    _ = -(u * (w * v)) := by simp only [neg_mul, mul_assoc]
    _ = -(u * (-(v * w))) := by rw [hwv]
    _ = u * (v * w) := by simp only [mul_neg, neg_neg]
    _ = (u * v) * w := by simp only [mul_assoc]

/-- Original axis 0 is incident to original Z=e0e1. -/
theorem originalAxis0_Z_anticomm (α : RealSpinBlock) :
    E α 0 * sourceZBivector α =
      -(sourceZBivector α * E α 0) := by
  change E α 0 * (E α 0 * E α 1) =
    -((E α 0 * E α 1) * E α 0)
  exact bivector_first_anticomm _ _
    (sourceAxis_anticomm α 1 0 (by decide))

theorem originalAxis1_Z_anticomm (α : RealSpinBlock) :
    E α 1 * sourceZBivector α =
      -(sourceZBivector α * E α 1) := by
  change E α 1 * (E α 0 * E α 1) =
    -((E α 0 * E α 1) * E α 1)
  exact bivector_second_anticomm _ _
    (sourceAxis_anticomm α 1 0 (by decide))

theorem originalAxis2_Z_comm (α : RealSpinBlock) :
    E α 2 * sourceZBivector α =
      sourceZBivector α * E α 2 := by
  change E α 2 * (E α 0 * E α 1) =
    (E α 0 * E α 1) * E α 2
  exact bivector_third_comm _ _ _
    (sourceAxis_anticomm α 2 0 (by decide))
    (sourceAxis_anticomm α 2 1 (by decide))

/-- Original positive-i Y=e2e0. -/
theorem originalAxis0_Y_anticomm (α : RealSpinBlock) :
    E α 0 * sourceYBivector α =
      -(sourceYBivector α * E α 0) := by
  change E α 0 * (E α 2 * E α 0) =
    -((E α 2 * E α 0) * E α 0)
  exact bivector_second_anticomm _ _
    (sourceAxis_anticomm α 0 2 (by decide))

theorem originalAxis1_Y_comm (α : RealSpinBlock) :
    E α 1 * sourceYBivector α =
      sourceYBivector α * E α 1 := by
  change E α 1 * (E α 2 * E α 0) =
    (E α 2 * E α 0) * E α 1
  exact bivector_third_comm _ _ _
    (sourceAxis_anticomm α 1 2 (by decide))
    (sourceAxis_anticomm α 1 0 (by decide))

theorem originalAxis2_Y_anticomm (α : RealSpinBlock) :
    E α 2 * sourceYBivector α =
      -(sourceYBivector α * E α 2) := by
  change E α 2 * (E α 2 * E α 0) =
    -((E α 2 * E α 0) * E α 2)
  exact bivector_first_anticomm _ _
    (sourceAxis_anticomm α 0 2 (by decide))

/-- Original positive-i X=e1e2. -/
theorem originalAxis0_X_comm (α : RealSpinBlock) :
    E α 0 * sourceXBivector α =
      sourceXBivector α * E α 0 := by
  change E α 0 * (E α 1 * E α 2) =
    (E α 1 * E α 2) * E α 0
  exact bivector_third_comm _ _ _
    (sourceAxis_anticomm α 0 1 (by decide))
    (sourceAxis_anticomm α 0 2 (by decide))

theorem originalAxis1_X_anticomm (α : RealSpinBlock) :
    E α 1 * sourceXBivector α =
      -(sourceXBivector α * E α 1) := by
  change E α 1 * (E α 1 * E α 2) =
    -((E α 1 * E α 2) * E α 1)
  exact bivector_first_anticomm _ _
    (sourceAxis_anticomm α 2 1 (by decide))

theorem originalAxis2_X_anticomm (α : RealSpinBlock) :
    E α 2 * sourceXBivector α =
      -(sourceXBivector α * E α 2) := by
  change E α 2 * (E α 1 * E α 2) =
    -((E α 1 * E α 2) * E α 2)
  exact bivector_second_anticomm _ _
    (sourceAxis_anticomm α 2 1 (by decide))

#print axioms originalAxis0_Z_anticomm
#print axioms originalAxis1_Z_anticomm
#print axioms originalAxis2_Z_comm
#print axioms originalAxis0_Y_anticomm
#print axioms originalAxis1_Y_comm
#print axioms originalAxis2_Y_anticomm
#print axioms originalAxis0_X_comm
#print axioms originalAxis1_X_anticomm
#print axioms originalAxis2_X_anticomm

end
end FCP.BFSSS1V52L9B0
