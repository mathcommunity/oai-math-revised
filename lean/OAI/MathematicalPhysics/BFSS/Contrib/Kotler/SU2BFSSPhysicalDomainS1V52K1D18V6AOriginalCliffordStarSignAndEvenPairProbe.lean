import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V5OriginalSourceUnitVectorNormalizationProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
K1D18V6A — exact source Clifford star sign and even two-vector
normalization. This is a mandatory sign-sensitive bridge before
claiming Pin or Spin membership.

IMPORTANT pinned Mathlib Clifford convention:
star (ι Q u) = -ι Q u, not ι Q u.
For source unit Q(u)=1, a single odd generator has
star(ι Q u)*ι Q u = -1, hence is NOT unitary.
The product of TWO such source generators has star norm +1.
Do not misclassify a single generator as Pin or Spin.

Candidate until source-pinned warning-as-error and exact axiom CI.
These theorems do not yet construct a genuine Spin element,
show image surjectivity, a topological covering, or BFSS spectra.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V6A
noncomputable section
open FCP.BFSSS1V0
open CliffordAlgebra

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- A source unit-Q vector gives an odd Clifford generator whose
actual Mathlib star norm is NEGATIVE one, so it is not itself Pin
unitary under the chosen pinned convention. -/
theorem source48_unitGenerator_star_mul_self_neg_one
    (u : Source48Vector) (hu : Q u = 1) :
    star (CliffordAlgebra.ι Q u) * (CliffordAlgebra.ι Q u) =
      (-1 : CliffordAlgebra Q) := by
  rw [CliffordAlgebra.star_ι, neg_mul, CliffordAlgebra.ι_sq_scalar, hu]
  simp

/-- The negative signs cancel for a genuine original Clifford pair.
First unitary equation of the product, retaining actual source Q. -/
theorem source48_twoUnitGenerators_star_mul_self
    (u v : Source48Vector) (hu : Q u = 1) (hv : Q v = 1) :
    star (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) *
      (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) = 1 := by
  calc
    star (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) *
        (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) =
        (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u) *
          (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) := by
            rw [star_mul, CliffordAlgebra.star_ι, CliffordAlgebra.star_ι]
            simp only [neg_mul_neg]
    _ = CliffordAlgebra.ι Q v *
          ((CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q u) *
            CliffordAlgebra.ι Q v) := by
            simp only [mul_assoc]
    _ = CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v := by
          rw [CliffordAlgebra.ι_sq_scalar, hu]
          simp
    _ = 1 := by rw [CliffordAlgebra.ι_sq_scalar, hv]; simp

/-- Second unitary equation, the reverse order, independently
checked on the true source Clifford pair. -/
theorem source48_twoUnitGenerators_mul_star_self
    (u v : Source48Vector) (hu : Q u = 1) (hv : Q v = 1) :
    (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) *
      star (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) = 1 := by
  calc
    (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) *
        star (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) =
        (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v) *
          (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u) := by
            rw [star_mul, CliffordAlgebra.star_ι, CliffordAlgebra.star_ι]
            simp only [neg_mul_neg]
    _ = CliffordAlgebra.ι Q u *
          ((CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v) *
            CliffordAlgebra.ι Q u) := by
            simp only [mul_assoc]
    _ = CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q u := by
          rw [CliffordAlgebra.ι_sq_scalar, hv]
          simp
    _ = 1 := by rw [CliffordAlgebra.ι_sq_scalar, hu]; simp

/-- The actual source Clifford pair lies in the actual even
subalgebra, independent of the Q-unit hypotheses. -/
theorem source48_twoGenerators_mem_even
    (u v : Source48Vector) :
    CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v ∈
      CliffordAlgebra.even Q := by
  change CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v ∈
    CliffordAlgebra.evenOdd Q 0
  exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q u v

/-- Genuine source two-generator product obeys both defining
unitary equations, but Lipschitz membership and Spin membership
remain separately verified source obligations. -/
theorem source48_twoUnitGenerators_mem_unitary
    (u v : Source48Vector) (hu : Q u = 1) (hv : Q v = 1) :
    CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v ∈
      unitary (CliffordAlgebra Q) := by
  exact ⟨source48_twoUnitGenerators_star_mul_self u v hu hv,
    source48_twoUnitGenerators_mul_star_self u v hu hv⟩

#print axioms source48_unitGenerator_star_mul_self_neg_one
#print axioms source48_twoUnitGenerators_star_mul_self
#print axioms source48_twoUnitGenerators_mul_star_self
#print axioms source48_twoGenerators_mem_even
#print axioms source48_twoUnitGenerators_mem_unitary

end
end FCP.BFSSS1V52K1D18V6A
