import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52B2Original48CliffordQuaternionPolynomialMulProbe
import Mathlib.Tactic.Ring

/-!
S1V52-B3: original-source 48-Clifford polynomial's exact quaternion
conjugation and algebraic invertibility on the real unit 3-sphere.

This imports strict-accepted A/B1/B2 and uses the GENUINE source
CliffordAlgebra source48Quadratic, not a surrogate algebra.
The unit norm is a proposition on real coordinates, not a new
SU2 group definition and not an assumed native GaugeGroup fact.
Cˣ is only the ambient Clifford unit group, NOT Mathlib spinGroup Q:
lipschitz, Pin, even and exact source action still require proof.

Candidate until qualified pinned strict CI with printed axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52B3
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Real conjugation of positive-i quaternion coordinates. -/
def sourceQuaternionConj (p : SourceQuaternionCoords) : SourceQuaternionCoords :=
  ⟨p.a, -p.b, -p.c, -p.d⟩

/-- The exact nonnegative real scalar quaternion norm squared. -/
def sourceQuaternionNormSq (p : SourceQuaternionCoords) : ℝ :=
  p.a ^ 2 + p.b ^ 2 + p.c ^ 2 + p.d ^ 2

theorem sourceQuaternionCompose_conj_right (p : SourceQuaternionCoords) :
    sourceQuaternionCompose p (sourceQuaternionConj p) =
      ⟨sourceQuaternionNormSq p, 0, 0, 0⟩ := by
  cases p with
  | mk a b c d =>
    simp only [sourceQuaternionCompose, sourceQuaternionConj,
      sourceQuaternionNormSq]
    congr 1 <;> ring

theorem sourceQuaternionCompose_conj_left (p : SourceQuaternionCoords) :
    sourceQuaternionCompose (sourceQuaternionConj p) p =
      ⟨sourceQuaternionNormSq p, 0, 0, 0⟩ := by
  cases p with
  | mk a b c d =>
    simp only [sourceQuaternionCompose, sourceQuaternionConj,
      sourceQuaternionNormSq]
    congr 1 <;> ring

/-- The actual original 48-source real Clifford quaternion polynomial
has the expected scalar product with its coordinate conjugate. -/
theorem sourceCliffordQuaternion_mul_conj (α : RealSpinBlock)
    (p : SourceQuaternionCoords) :
    sourceCliffordQuaternion α p *
      sourceCliffordQuaternion α (sourceQuaternionConj p) =
        sourceQuaternionNormSq p • (1 : C) := by
  rw [← sourceCliffordQuaternion_compose,
    sourceQuaternionCompose_conj_right]
  simp [sourceCliffordQuaternion]

theorem sourceCliffordQuaternion_conj_mul (α : RealSpinBlock)
    (p : SourceQuaternionCoords) :
    sourceCliffordQuaternion α (sourceQuaternionConj p) *
      sourceCliffordQuaternion α p =
        sourceQuaternionNormSq p • (1 : C) := by
  rw [← sourceCliffordQuaternion_compose,
    sourceQuaternionCompose_conj_left]
  simp [sourceCliffordQuaternion]

/-- A norm-one quaternion polynomial is a unit in the genuine source
48-Clifford algebra. Not yet an element of Mathlib's spinGroup. -/
noncomputable def sourceCliffordQuaternionUnit (α : RealSpinBlock)
    (p : SourceQuaternionCoords) (hp : sourceQuaternionNormSq p = 1) :
    Cˣ :=
  ⟨sourceCliffordQuaternion α p,
    sourceCliffordQuaternion α (sourceQuaternionConj p),
    by
      rw [sourceCliffordQuaternion_mul_conj, hp, one_smul],
    by
      rw [sourceCliffordQuaternion_conj_mul, hp, one_smul]⟩

theorem sourceCliffordQuaternionUnit_coe
    (α : RealSpinBlock) (p : SourceQuaternionCoords)
    (hp : sourceQuaternionNormSq p = 1) :
    (sourceCliffordQuaternionUnit α p hp : C) =
      sourceCliffordQuaternion α p := rfl

#print axioms sourceQuaternionCompose_conj_right
#print axioms sourceQuaternionCompose_conj_left
#print axioms sourceCliffordQuaternion_mul_conj
#print axioms sourceCliffordQuaternion_conj_mul
#print axioms sourceCliffordQuaternionUnit
#print axioms sourceCliffordQuaternionUnit_coe

end
end FCP.BFSSS1V52B3
