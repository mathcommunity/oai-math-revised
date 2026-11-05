import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8POriginalSU2UnitaryQuaternionMatrixFormProbe
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Basic.Complex.Basic

/-!
L6H5E8Q — exact source SU2 quaternion matrix FORM and UNIT NORM
as separate, auditable concrete finite-dimensional constraints.

H5E8P #339 (qualified) gave adjugate(g) = gᴴ and the two
dependent entries of every genuine GaugeGroup 2 matrix.
This new gate packages the *whole* literal 2x2 matrix and
derives the complex row norm identity and its real-valued
normSq equality, prerequisites for an exact source-color
Euler-angle factorization.

NO source color curve generation, connectedness or gauge
physical-space equivalence is assumed by the new proofs.
No new axioms, different +i sign, or Fock surrogate action.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8Q
noncomputable section
open OAI.BFSSQuantum
open FCP.BFSSSU2PhysicalDomainL6H5E8P
open Matrix

/-- The exact original SU2 matrix, not just separate entry
identities, is in the standard quaternionic 2x2 form. -/
theorem originalSU2_quaternion_matrix
    (g : GaugeGroup 2) :
    (g : ColorMatrix 2) =
      !![(g : ColorMatrix 2) 0 0, (g : ColorMatrix 2) 0 1;
         -star ((g : ColorMatrix 2) 0 1),
         star ((g : ColorMatrix 2) 0 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalSU2_bottomRight_eq_conj_topLeft,
      originalSU2_bottomLeft_eq_neg_conj_topRight]

/-- The first original unitary SU2 row has complex scalar
norm one, extracted without any color/Fock unfolding. -/
theorem originalSU2_firstRow_star_norm
    (g : GaugeGroup 2) :
    (g : ColorMatrix 2) 0 0 * star ((g : ColorMatrix 2) 0 0) +
      (g : ColorMatrix 2) 0 1 * star ((g : ColorMatrix 2) 0 1) =
        (1 : ℂ) := by
  let A : ColorMatrix 2 := g
  have hu : A * Aᴴ = (1 : ColorMatrix 2) := by
    have hm : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := g.property.1
    simpa only [Matrix.star_eq_conjTranspose] using hm.2
  have he := congrArg (fun M : ColorMatrix 2 => M 0 0) hu
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using he

/-- Quaternionic coordinates (u,v) of the actual SU2
matrix lie on the real unit 3-sphere. This is
necessary for the later polar/Euler angle witnesses. -/
theorem originalSU2_firstRow_normSq_eq_one
    (g : GaugeGroup 2) :
    Complex.normSq ((g : ColorMatrix 2) 0 0) +
      Complex.normSq ((g : ColorMatrix 2) 0 1) = 1 := by
  let u : ℂ := (g : ColorMatrix 2) 0 0
  let v : ℂ := (g : ColorMatrix 2) 0 1
  have hrow : u * star u + v * star v = 1 :=
    originalSU2_firstRow_star_norm g
  have hcast :
      ((Complex.normSq u : ℝ) : ℂ) +
        ((Complex.normSq v : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_conj_mul_self]
    -- Pinned Mathlib defines Complex conjugation via `star`; there is no
    -- `Complex.conj` constant. Avoid that nonexistent identifier entirely.
    change star u * u + star v * v = 1
    calc
      star u * u + star v * v =
        u * star u + v * star v := by ring
      _ = 1 := hrow
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_add, Complex.ofReal_one] using hcast

#print axioms originalSU2_quaternion_matrix
#print axioms originalSU2_firstRow_star_norm
#print axioms originalSU2_firstRow_normSq_eq_one
#check @originalSU2_firstRow_normSq_eq_one

end
end FCP.BFSSSU2PhysicalDomainL6H5E8Q
