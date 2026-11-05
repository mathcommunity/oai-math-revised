import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9B3OriginalBivectorOnAxisReductionProbe
import Mathlib.Tactic.Module

/-!
S1V52-L9B4 — STAGED, UNQUALIFIED explicit original-source 48-Clifford
same-block quaternion star-conjugation on each of three genuine source
Majorana color axes.

This is the desired local Clifford spin-action identity with explicit
real 3×3 quaternion polynomial coefficients, using ONLY exact source
coordinates and already staged L9B1 (star reflection), L9B2 (finite
quaternion coordinate products), and L9B3 (six bivector-axis reductions).
The source coefficients must subsequently be shown to equal the actual
pinned G3A `adjointColorMatrix g`, for g : OAI.BFSSQuantum.GaugeGroup 2.

This stage does NOT claim acceptance before pinned strict CI, does
NOT substitute a new real SU2 group, does NOT derive continuity,
does NOT yet construct a full sixteen-block physical Majorana action,
Fock intertwiner, original manuscript Hamiltonian, or spectral theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 420000

namespace FCP.BFSSS1V52L9B4
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52L9B1
open FCP.BFSSS1V52L9B2
open FCP.BFSSS1V52L9B3

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev E (α : RealSpinBlock) (i : Fin 3) : C :=
  CliffordAlgebra.ι Q (sourceBlockColorAxis α i)

/-- The first ORIGINAL Majorana axis transforms in the first column
of the true source positive-i quaternion rotation polynomial. -/
theorem originalSameBlockQuaternion_conj_axis0
    (α : RealSpinBlock) (p : SourceQuaternionCoords) :
    sourceCliffordQuaternion α p * E α 0 *
      star (sourceCliffordQuaternion α p) =
        (p.a^2-p.b^2-p.c^2+p.d^2) • E α 0 +
        (-2*p.a*p.b+2*p.c*p.d) • E α 1 +
        (2*p.a*p.c+2*p.b*p.d) • E α 2 := by
  calc
    sourceCliffordQuaternion α p * E α 0 *
        star (sourceCliffordQuaternion α p) =
      sourceCliffordQuaternion α p *
        (E α 0 * star (sourceCliffordQuaternion α p)) := by
          simp only [mul_assoc]
    _ = sourceCliffordQuaternion α p *
        (sourceCliffordQuaternion α ⟨p.a,p.b,p.c,-p.d⟩ * E α 0) := by
          rw [originalAxis0_star_quaternion_reflection]
    _ = (sourceCliffordQuaternion α p *
        sourceCliffordQuaternion α ⟨p.a,p.b,p.c,-p.d⟩) * E α 0 := by
          simp only [mul_assoc]
    _ = sourceCliffordQuaternion α
        (sourceQuaternionCompose p ⟨p.a,p.b,p.c,-p.d⟩) * E α 0 := by
          rw [sourceCliffordQuaternion_compose]
    _ = sourceCliffordQuaternion α
        ⟨p.a^2-p.b^2-p.c^2+p.d^2,
         2*p.a*p.b-2*p.c*p.d,
         2*p.a*p.c+2*p.b*p.d, 0⟩ * E α 0 := by
          rw [originalQuat_axis0_reflect_compose]
    _ = (p.a^2-p.b^2-p.c^2+p.d^2) • E α 0 +
        (-2*p.a*p.b+2*p.c*p.d) • E α 1 +
        (2*p.a*p.c+2*p.b*p.d) • E α 2 := by
          change ((p.a^2-p.b^2-p.c^2+p.d^2) • (1 : C) +
            (2*p.a*p.b-2*p.c*p.d) • sourceZBivector α +
            (2*p.a*p.c+2*p.b*p.d) • sourceYBivector α +
            (0 : ℝ) • sourceXBivector α) * E α 0 = _
          simp only [add_mul, smul_mul_assoc, one_mul,
            originalZ_mul_axis0, originalY_mul_axis0,
            smul_neg, zero_smul, add_zero]
          module

/-- Second color axis, preserving rows=output, columns=input. -/
theorem originalSameBlockQuaternion_conj_axis1
    (α : RealSpinBlock) (p : SourceQuaternionCoords) :
    sourceCliffordQuaternion α p * E α 1 *
      star (sourceCliffordQuaternion α p) =
        (2*p.a*p.b+2*p.c*p.d) • E α 0 +
        (p.a^2-p.b^2+p.c^2-p.d^2) • E α 1 +
        (-2*p.a*p.d+2*p.b*p.c) • E α 2 := by
  calc
    sourceCliffordQuaternion α p * E α 1 *
        star (sourceCliffordQuaternion α p) =
      sourceCliffordQuaternion α p *
        (E α 1 * star (sourceCliffordQuaternion α p)) := by
          simp only [mul_assoc]
    _ = sourceCliffordQuaternion α p *
        (sourceCliffordQuaternion α ⟨p.a,p.b,-p.c,p.d⟩ * E α 1) := by
          rw [originalAxis1_star_quaternion_reflection]
    _ = (sourceCliffordQuaternion α p *
        sourceCliffordQuaternion α ⟨p.a,p.b,-p.c,p.d⟩) * E α 1 := by
          simp only [mul_assoc]
    _ = sourceCliffordQuaternion α
        (sourceQuaternionCompose p ⟨p.a,p.b,-p.c,p.d⟩) * E α 1 := by
          rw [sourceCliffordQuaternion_compose]
    _ = sourceCliffordQuaternion α
        ⟨p.a^2-p.b^2+p.c^2-p.d^2,
         2*p.a*p.b+2*p.c*p.d, 0,
         2*p.a*p.d-2*p.b*p.c⟩ * E α 1 := by
          rw [originalQuat_axis1_reflect_compose]
    _ = (2*p.a*p.b+2*p.c*p.d) • E α 0 +
        (p.a^2-p.b^2+p.c^2-p.d^2) • E α 1 +
        (-2*p.a*p.d+2*p.b*p.c) • E α 2 := by
          change ((p.a^2-p.b^2+p.c^2-p.d^2) • (1 : C) +
            (2*p.a*p.b+2*p.c*p.d) • sourceZBivector α +
            (0 : ℝ) • sourceYBivector α +
            (2*p.a*p.d-2*p.b*p.c) • sourceXBivector α) * E α 1 = _
          simp only [add_mul, smul_mul_assoc, one_mul,
            originalZ_mul_axis1, originalX_mul_axis1,
            smul_neg, zero_smul, add_zero]
          module

/-- Third color axis, with original +i and real Fock label order. -/
theorem originalSameBlockQuaternion_conj_axis2
    (α : RealSpinBlock) (p : SourceQuaternionCoords) :
    sourceCliffordQuaternion α p * E α 2 *
      star (sourceCliffordQuaternion α p) =
        (-2*p.a*p.c+2*p.b*p.d) • E α 0 +
        (2*p.a*p.d+2*p.b*p.c) • E α 1 +
        (p.a^2+p.b^2-p.c^2-p.d^2) • E α 2 := by
  calc
    sourceCliffordQuaternion α p * E α 2 *
        star (sourceCliffordQuaternion α p) =
      sourceCliffordQuaternion α p *
        (E α 2 * star (sourceCliffordQuaternion α p)) := by
          simp only [mul_assoc]
    _ = sourceCliffordQuaternion α p *
        (sourceCliffordQuaternion α ⟨p.a,-p.b,p.c,p.d⟩ * E α 2) := by
          rw [originalAxis2_star_quaternion_reflection]
    _ = (sourceCliffordQuaternion α p *
        sourceCliffordQuaternion α ⟨p.a,-p.b,p.c,p.d⟩) * E α 2 := by
          simp only [mul_assoc]
    _ = sourceCliffordQuaternion α
        (sourceQuaternionCompose p ⟨p.a,-p.b,p.c,p.d⟩) * E α 2 := by
          rw [sourceCliffordQuaternion_compose]
    _ = sourceCliffordQuaternion α
        ⟨p.a^2+p.b^2-p.c^2-p.d^2,
         0, 2*p.a*p.c-2*p.b*p.d,
         2*p.a*p.d+2*p.b*p.c⟩ * E α 2 := by
          rw [originalQuat_axis2_reflect_compose]
    _ = (-2*p.a*p.c+2*p.b*p.d) • E α 0 +
        (2*p.a*p.d+2*p.b*p.c) • E α 1 +
        (p.a^2+p.b^2-p.c^2-p.d^2) • E α 2 := by
          change ((p.a^2+p.b^2-p.c^2-p.d^2) • (1 : C) +
            (0 : ℝ) • sourceZBivector α +
            (2*p.a*p.c-2*p.b*p.d) • sourceYBivector α +
            (2*p.a*p.d+2*p.b*p.c) • sourceXBivector α) * E α 2 = _
          simp only [add_mul, smul_mul_assoc, one_mul,
            originalY_mul_axis2, originalX_mul_axis2,
            smul_neg, zero_smul, add_zero]
          module

#print axioms originalSameBlockQuaternion_conj_axis0
#print axioms originalSameBlockQuaternion_conj_axis1
#print axioms originalSameBlockQuaternion_conj_axis2

end
end FCP.BFSSS1V52L9B4
