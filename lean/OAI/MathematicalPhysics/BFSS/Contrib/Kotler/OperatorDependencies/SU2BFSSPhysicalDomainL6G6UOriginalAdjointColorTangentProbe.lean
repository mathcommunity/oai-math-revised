import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6DOriginalFermionResponseSymmetricLegsProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG3CComplexOneParticleUnitaryProbe

/-!
L6G6U — source-defined adjoint-color *candidate tangent*,
with the exact original SU(2) color indices and sign.

This is a genuine source identity needed to compute the first variation
of the CONSTRUCTED gauge representation. The pinned source defines
the Hermitian color Lie bracket by -i [T_a, T_b]. Accordingly the
matrix trace coefficient of +i [T_c, T_A], with output color B and
input A, is f_(B A c).

The finite-dimensional matrix and its eight-block 24-mode extension
are the exact expected right-hand sides for differentiating the
source adjoint SU(2) action g(t)=exp(+i t T_c).

Crucial boundary: this module does NOT construct g(t) inside
GaugeGroup 2 or prove a HasDerivAt/HasFDerivAt statement for its
actual adjointCoefficient, G3C complexOneParticleMatrix, exterior
G4A action, or G4B/G4J fermion action. This is the algebraic tangent
coefficient, not a derivative identification or a Gauss theorem.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6U
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A

/-- The +i commutator is the negative of the literal pinned
Hermitian source bracket; the sign is determined by Core.lean. -/
private theorem plusI_comm_eq_neg_sourceBracket
    (X Y : ColorMatrix 2) :
    (Complex.I : ℂ) • (X * Y - Y * X) =
      -(AlgebraData.bracket X Y) := by
  simp only [AlgebraData.bracket, neg_smul, neg_neg]

/-- Matrix coefficient of the source +i infinitesimal color
conjugation. Matrix row B is OUTPUT and column A is INPUT, agreeing
with accepted G3A/G3B/G3C matrices. This definition alone does not
claim it is a derivative of a special-unitary group curve. -/
noncomputable def sourceAdjointColorCandidateTangent
    (M : AlgebraData 2) (c : ColorIndex 2) :
    Matrix (ColorIndex 2) (ColorIndex 2) ℝ :=
  fun B A =>
    (Matrix.trace
      (M.color B *
        ((Complex.I : ℂ) •
          (M.color c * M.color A - M.color A * M.color c)))).re

/-- Falsifiable source sign and index orientation:
the +i adjoint tangent coefficient equals the ORIGINAL
source structure constant f_(B A c). -/
theorem sourceAdjointColorCandidateTangent_coeff
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (c B A : ColorIndex 2) :
    sourceAdjointColorCandidateTangent M c B A =
      M.structureConstant B A c := by
  unfold sourceAdjointColorCandidateTangent
  rw [plusI_comm_eq_neg_sourceBracket, mul_neg,
      Matrix.trace_neg, Complex.neg_re]
  change -(M.structureConstant B c A) = M.structureConstant B A c
  rw [FCP.BFSSSU2PhysicalDomainL6G6D.sourceSU2StructureConstant_swapLast
    M hcolor B A c]
  simp

/-- The exact candidate tangent matrix is real skew-symmetric,
as a source consequence of the accepted first-two color skewness. -/
theorem sourceAdjointColorCandidateTangent_skew
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (c A B : ColorIndex 2) :
    sourceAdjointColorCandidateTangent M c B A =
      -sourceAdjointColorCandidateTangent M c A B := by
  rw [sourceAdjointColorCandidateTangent_coeff M hcolor,
      sourceAdjointColorCandidateTangent_coeff M hcolor]
  exact
    FCP.BFSSSU2PhysicalDomainL6G6D.sourceSU2StructureConstant_swapFirst
      M hcolor A B c

/-- The actual original AlgebraData 2 witness fixes precisely the
coefficient that must arise from differentiating the true G3A
adjoint matrix with output color B, input A. -/
theorem pairedSourceAdjointColorCandidateTangent_coeff
    (c B A : ColorIndex 2) :
    sourceAdjointColorCandidateTangent pairedAlgebraData c B A =
      pairedAlgebraData.structureConstant B A c := by
  exact sourceAdjointColorCandidateTangent_coeff pairedAlgebraData
    pairedAlgebraData_color c B A

/-- Lift exactly the same source Lie-algebra coefficient to the 24
real/imaginary-paired source Fock modes, with no inter-pair mixing.
This is the expected one-particle derivative matrix, NOT a claim
that the genuine group matrix has yet been differentiated. -/
noncomputable def source24ModeCandidateTangent
    (c : ColorIndex 2) : Matrix (Fin 24) (Fin 24) ℂ :=
  fun m n =>
    if (colorModeEquiv.symm m).1 = (colorModeEquiv.symm n).1 then
      ((sourceAdjointColorCandidateTangent pairedAlgebraData c
          (colorModeEquiv.symm m).2 (colorModeEquiv.symm n).2 : ℝ) : ℂ)
    else 0

/-- The eight source spin-pair blocks have the correct exact input/
output coefficient f_(B A c). All off-block entries vanish. -/
theorem source24ModeCandidateTangent_block
    (c : ColorIndex 2) (j k : Fin 8) (B A : ColorIndex 2) :
    source24ModeCandidateTangent c
      (colorModeEquiv (j,B)) (colorModeEquiv (k,A)) =
    if j = k then (pairedAlgebraData.structureConstant B A c : ℂ)
      else 0 := by
  simp only [source24ModeCandidateTangent, Equiv.symm_apply_apply]
  by_cases h : j = k
  · simp only [_root_.ite_eq_left h]
    exact congrArg (fun r : ℝ => (r : ℂ))
      (pairedSourceAdjointColorCandidateTangent_coeff c B A)
  · simp only [_root_.ite_eq_right h]

#print axioms plusI_comm_eq_neg_sourceBracket
#print axioms sourceAdjointColorCandidateTangent_coeff
#print axioms sourceAdjointColorCandidateTangent_skew
#print axioms pairedSourceAdjointColorCandidateTangent_coeff
#print axioms source24ModeCandidateTangent_block
#check @source24ModeCandidateTangent_block

end
end FCP.BFSSSU2PhysicalDomainL6G6U
