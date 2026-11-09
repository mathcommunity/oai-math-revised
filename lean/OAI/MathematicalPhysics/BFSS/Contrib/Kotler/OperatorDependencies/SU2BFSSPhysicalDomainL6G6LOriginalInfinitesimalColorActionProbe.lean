import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6KOriginalBoundedFermionColorCurrentProbe

/-!
L6G6L — original infinitesimal fermionic SU(2) color action.

The bounded Hermitian source current G_F is already certified by L6G6K.
The skew-adjoint candidate generator J_F := i G_F therefore has a
specific, NEGATIVE infinitesimal commutator sign on the original
48 Majoranas. The same assertion holds on the true source SmoothCore,
without swapping the two representations or reversing color indices.

This is not yet the identity between J_F and the derivative of the
actual G4E/G4J gauge representation. A shared covariance equation
determines an implementer only up to a central scalar. Identifying
that scalar requires vacuum normalization and a genuine gauge curve.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G6L
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G6I
open FCP.BFSSSU2PhysicalDomainL6G6J
open FCP.BFSSSU2PhysicalDomainL6G6K

/-- Scalar transport of a CAR current commutator. This is the only
ring-algebra step; the genuine source current is supplied separately. -/
private theorem complexI_comm_of_current_comm
    {R : Type*} [Ring R] [Algebra ℂ R]
    (G T X : R)
    (h : G * T - T * G = Complex.I • X) :
    (Complex.I • G) * T - T * (Complex.I • G) = -X := by
  calc
    _ = Complex.I • (G * T - T * G) := by
          rw [smul_mul_assoc, mul_smul_comm, smul_sub]
    _ = (Complex.I * Complex.I) • X := by
          rw [h, smul_smul]
    _ = -X := by
          rw [Complex.I_mul_I, neg_smul, one_smul]

/-- The literal original bounded Fock generator acts on each of the
48 source Majoranas with the NEGATIVE color-index coefficient.
No gauge-representation identification is assumed. -/
theorem sourceFiberFermionColorGenerator_comm
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (c : ColorIndex 2) (t : SpinIndex) (d : ColorIndex 2) :
    sourceFiberFermionColorGenerator M c * M.theta t d -
      M.theta t d * sourceFiberFermionColorGenerator M c =
      -(∑ b : ColorIndex 2,
        (M.structureConstant d b c : ℂ) • M.theta t b) := by
  unfold sourceFiberFermionColorGenerator
  exact complexI_comm_of_current_comm
    (sourceFiberFermionColorCurrent M c) (M.theta t d)
    (∑ b : ColorIndex 2,
      (M.structureConstant d b c : ℂ) • M.theta t b)
    (sourceFiberFermionColorCurrent_comm M hcolor c t d)

/-- Identical sign on the genuine ORIGINAL SmoothCore operators, not
an inferred equivalence between a proxy Fock model and source space. -/
theorem sourceOriginalFermionColorGenerator_comm
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (c : ColorIndex 2) (t : SpinIndex) (d : ColorIndex 2) :
    (Complex.I • sourceOriginalFermionColorCurrent M c) *
        M.fermionAction t d -
      M.fermionAction t d *
        (Complex.I • sourceOriginalFermionColorCurrent M c) =
      -(∑ b : ColorIndex 2,
        (M.structureConstant d b c : ℂ) • M.fermionAction t b) := by
  exact complexI_comm_of_current_comm
    (sourceOriginalFermionColorCurrent M c) (M.fermionAction t d)
    (∑ b : ColorIndex 2,
      (M.structureConstant d b c : ℂ) • M.fermionAction t b)
    (sourceOriginalFermionColorCurrent_comm M hcolor c t d)

#print axioms complexI_comm_of_current_comm
#print axioms sourceFiberFermionColorGenerator_comm
#print axioms sourceOriginalFermionColorGenerator_comm
#check @sourceFiberFermionColorGenerator_comm
#check @sourceOriginalFermionColorGenerator_comm

end
end FCP.BFSSSU2PhysicalDomainL6G6L
