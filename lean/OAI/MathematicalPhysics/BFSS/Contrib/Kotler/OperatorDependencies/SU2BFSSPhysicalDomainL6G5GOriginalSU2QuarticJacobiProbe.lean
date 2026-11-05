import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5FSourceQuarticPointwiseProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2ColorCrossProbe

/-!
L6G5G — real SU(2) color bracket as a SIMPLE bivector.

The original pinned Pauli color source, rather than an invented epsilon
tensor, gives f_{abc}=sqrt(2) epsilon3. Each fixed-color original source
coordinateBracketAll is therefore sqrt(2) times a decomposable
two-form. The Pluecker identity is the exact four-index (Jacobi/Bianchi)
cancellation needed when squaring Clifford gammaTwo combinations.

This is a finite source color theorem, NOT YET the gammaTwo norm,
source quadratic square = bosonic potential, Gauss, or spectrum.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G5G
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G5F

/-- Universal rank-two Pluecker relation; no color assumptions. -/
private theorem simpleBivector_plucker
    {I : Type*} (u v : I → ℝ) (i j k l : I) :
    (u i * v j - u j * v i) * (u k * v l - u l * v k) -
    (u i * v k - u k * v i) * (u j * v l - u l * v j) +
    (u i * v l - u l * v i) * (u j * v k - u k * v j) = 0 := by
  ring

/-- This is the original source bracket, evaluated in its accepted Pauli
color basis. The equality to a sqrt2 color cross product is obtained from
the independently accepted concrete SU(2) source theorem. -/
theorem sourceSU2Bracket_eq_cross
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2, M.color a = FCP.BFSSSU2.normalizedPauli a)
    (x : Boson 2) (i j : SpaceIndex) (a : ColorIndex 2) :
    M.coordinateBracketAll x i j a =
      Real.sqrt 2 *
      FCP.BFSSSU2.colorCross
        (fun b : Fin 3 => x (i,b))
        (fun c : Fin 3 => x (j,c)) a := by
  unfold coordinateBracketAll
  simp_rw [FCP.BFSSSU2.algebraData_structureConstant_of_pauli_color M hcolor]
  exact FCP.BFSSSU2.epsilon3_contraction _ _ a

/-- Four-index Bianchi cancellation at *each actual SU(2) color label*,
not merely after summing colors. It is the Pluecker consequence of the
original Pauli source structure constants f=sqrt(2) epsilon. -/
theorem sourceSU2Bracket_plucker
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2, M.color a = FCP.BFSSSU2.normalizedPauli a)
    (x : Boson 2) (a : ColorIndex 2)
    (i j k l : SpaceIndex) :
    M.coordinateBracketAll x i j a * M.coordinateBracketAll x k l a -
    M.coordinateBracketAll x i k a * M.coordinateBracketAll x j l a +
    M.coordinateBracketAll x i l a * M.coordinateBracketAll x j k a = 0 := by
  simp only [sourceSU2Bracket_eq_cross M hcolor]
  fin_cases a <;> simp only [FCP.BFSSSU2.colorCross] <;> ring

#print axioms simpleBivector_plucker
#print axioms sourceSU2Bracket_eq_cross
#print axioms sourceSU2Bracket_plucker
#check @sourceSU2Bracket_plucker

end
end FCP.BFSSSU2PhysicalDomainL6G5G
