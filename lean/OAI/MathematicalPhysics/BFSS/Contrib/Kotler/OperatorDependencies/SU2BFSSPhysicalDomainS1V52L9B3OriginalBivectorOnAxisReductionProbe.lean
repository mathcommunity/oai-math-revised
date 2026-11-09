import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9B2OriginalQuaternionReflectionCoefficientProbe

/-!
S1V52-L9B3 — STAGED and UNQUALIFIED original source bivector-on-axis
reduction. No workflow is introduced by this source commit.

The six exact source identities reduce products of the original
positive-i Z=e0e1, Y=e2e0, X=e1e2 source 48-Clifford bivectors
against incident genuine source Majorana axes. Together with
L9B1 reflection and L9B2 coefficient identities they provide the
local algebraic bridge to exact original source Clifford conjugation.

The proof is deliberately in the noncommutative source Clifford
algebra, using qualified A axis unit and anti-commutation lemmas.
No 3-D substitute, no global commutativity, no new axioms or
surrogate gauge/Fock action. Future qualification requires a
strict source-pinned six-root CI using the ACCEPTED L9B2 cache.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSS1V52L9B3
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev E (α : RealSpinBlock) (i : Fin 3) : C :=
  CliffordAlgebra.ι Q (sourceBlockColorAxis α i)

/-- A bivector times its FIRST generating axis reverses the second,
provided the source axes anticommute and the first has Q-norm one. -/
private theorem pair_mul_first (u v : C)
    (hvu : v * u = -(u * v))
    (huu : u * u = 1) :
    (u * v) * u = -v := by
  calc
    (u * v) * u = u * (v * u) := by simp only [mul_assoc]
    _ = u * (-(u * v)) := by rw [hvu]
    _ = -((u * u) * v) := by simp only [mul_neg, mul_assoc]
    _ = -v := by rw [huu, one_mul]

/-- A bivector times its SECOND source generating axis gives the first. -/
private theorem pair_mul_second (u v : C)
    (hvv : v * v = 1) :
    (u * v) * v = u := by
  calc
    (u * v) * v = u * (v * v) := by simp only [mul_assoc]
    _ = u := by rw [hvv, mul_one]

theorem originalZ_mul_axis0 (α : RealSpinBlock) :
    sourceZBivector α * E α 0 = -(E α 1) := by
  change (E α 0 * E α 1) * E α 0 = -(E α 1)
  exact pair_mul_first _ _
    (sourceAxis_anticomm α 1 0 (by decide))
    (sourceAxis_square α 0)

theorem originalZ_mul_axis1 (α : RealSpinBlock) :
    sourceZBivector α * E α 1 = E α 0 := by
  change (E α 0 * E α 1) * E α 1 = E α 0
  exact pair_mul_second _ _ (sourceAxis_square α 1)

theorem originalY_mul_axis0 (α : RealSpinBlock) :
    sourceYBivector α * E α 0 = E α 2 := by
  change (E α 2 * E α 0) * E α 0 = E α 2
  exact pair_mul_second _ _ (sourceAxis_square α 0)

theorem originalY_mul_axis2 (α : RealSpinBlock) :
    sourceYBivector α * E α 2 = -(E α 0) := by
  change (E α 2 * E α 0) * E α 2 = -(E α 0)
  exact pair_mul_first _ _
    (sourceAxis_anticomm α 0 2 (by decide))
    (sourceAxis_square α 2)

theorem originalX_mul_axis1 (α : RealSpinBlock) :
    sourceXBivector α * E α 1 = -(E α 2) := by
  change (E α 1 * E α 2) * E α 1 = -(E α 2)
  exact pair_mul_first _ _
    (sourceAxis_anticomm α 2 1 (by decide))
    (sourceAxis_square α 1)

theorem originalX_mul_axis2 (α : RealSpinBlock) :
    sourceXBivector α * E α 2 = E α 1 := by
  change (E α 1 * E α 2) * E α 2 = E α 1
  exact pair_mul_second _ _ (sourceAxis_square α 2)

#print axioms originalZ_mul_axis0
#print axioms originalZ_mul_axis1
#print axioms originalY_mul_axis0
#print axioms originalY_mul_axis2
#print axioms originalX_mul_axis1
#print axioms originalX_mul_axis2

end
end FCP.BFSSS1V52L9B3
