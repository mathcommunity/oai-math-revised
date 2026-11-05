import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52B3Original48CliffordQuaternionUnitNormProbe

/-!
S1V52-S1: source-faithful STAR/UNITARY subobligation of Spin(48)
membership, strictly inside the genuine source original 48-Clifford
algebra (Q = source48Quadratic, original 16 × 3 Majorana axes).

IMPORTANT PINNED MATHLIB CONVENTION: CliffordAlgebra.star_ι m
is -ι Q m, and star reverses multiplication. An even bivector
from two orthogonal original positive-norm vectors is therefore
STAR-ANTI-SELFADJOINT, as required for real quaternion conjugation.

The source's accepted B3 inverse by quaternion conjugation is
not AUTOMATICALLY star-unitarity; this candidate establishes
exactly that extra equality and the resulting two-sided inverses
on norm-one coefficients. It does NOT establish Lipschitz subgroup
membership, evenness, Spin membership, projection or continuity.

This is a STAGED RESEARCH CANDIDATE ONLY; its theorem roots are
unaccepted until a dedicated strict pinned Lean and #print axioms CI.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.BFSSS1V52S1
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52B3

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Anti-self-adjoint source positive-i Z bivector. -/
theorem sourceZBivector_star (α : RealSpinBlock) :
    star (sourceZBivector α) = -sourceZBivector α := by
  dsimp [sourceZBivector]
  rw [star_mul, CliffordAlgebra.star_ι, CliffordAlgebra.star_ι]
  simpa only [neg_mul_neg] using
    (sourceAxis_anticomm α 1 0 (by decide))

/-- Anti-self-adjoint source positive-i Y bivector. -/
theorem sourceYBivector_star (α : RealSpinBlock) :
    star (sourceYBivector α) = -sourceYBivector α := by
  dsimp [sourceYBivector]
  rw [star_mul, CliffordAlgebra.star_ι, CliffordAlgebra.star_ι]
  simpa only [neg_mul_neg] using
    (sourceAxis_anticomm α 0 2 (by decide))

/-- Anti-self-adjoint source positive-i X bivector. -/
theorem sourceXBivector_star (α : RealSpinBlock) :
    star (sourceXBivector α) = -sourceXBivector α := by
  dsimp [sourceXBivector]
  rw [star_mul, CliffordAlgebra.star_ι, CliffordAlgebra.star_ι]
  simpa only [neg_mul_neg] using
    (sourceAxis_anticomm α 2 1 (by decide))

/-- Real quaternion conjugation corresponds exactly to the pinned
genuine 48-source Clifford star operation, not an invented inverse. -/
theorem sourceCliffordQuaternion_star_eq_conj (α : RealSpinBlock)
    (p : SourceQuaternionCoords) :
    star (sourceCliffordQuaternion α p) =
      sourceCliffordQuaternion α (sourceQuaternionConj p) := by
  simp [sourceCliffordQuaternion, sourceQuaternionConj,
    CliffordAlgebra.star_smul,
    sourceZBivector_star, sourceYBivector_star, sourceXBivector_star]

/-- Norm-one real quaternion source polynomial is genuinely
star-unitary in original 48-Clifford algebra, forward direction. -/
theorem sourceCliffordQuaternion_star_mul
    (α : RealSpinBlock) (p : SourceQuaternionCoords)
    (hp : sourceQuaternionNormSq p = 1) :
    star (sourceCliffordQuaternion α p) *
      sourceCliffordQuaternion α p = 1 := by
  rw [sourceCliffordQuaternion_star_eq_conj,
    sourceCliffordQuaternion_conj_mul, hp, one_smul]

/-- Genuine source Clifford star-unitarity, reverse direction. -/
theorem sourceCliffordQuaternion_mul_star
    (α : RealSpinBlock) (p : SourceQuaternionCoords)
    (hp : sourceQuaternionNormSq p = 1) :
    sourceCliffordQuaternion α p *
      star (sourceCliffordQuaternion α p) = 1 := by
  rw [sourceCliffordQuaternion_star_eq_conj,
    sourceCliffordQuaternion_mul_conj, hp, one_smul]

#print axioms sourceZBivector_star
#print axioms sourceYBivector_star
#print axioms sourceXBivector_star
#print axioms sourceCliffordQuaternion_star_eq_conj
#print axioms sourceCliffordQuaternion_star_mul
#print axioms sourceCliffordQuaternion_mul_star

end
end FCP.BFSSS1V52S1
