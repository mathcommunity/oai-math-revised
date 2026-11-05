import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6BOriginalFermionicFierzColorContractionProbe

/-!
L6G6C — original source fermionic response: eliminate the TWO
derivative-of-quadratic Kronecker selectors BEFORE gamma/color algebra.

The accepted L6G6A theorem identifies the literal original
SmoothCore coefficient commutator with its pointwise polynomial;
L6G6B separately proves the signed source gamma/color Fierz channels.
This gate transforms G6A's point coefficient into TWO explicit
finite contractions over the original kinetic and quadratic weights.

Both derivative positions are retained, including their signs.
No structural-constant antisymmetry, synthetic replacement operators,
unproved Fierz hypothesis, operator reordering, or physical
gauge constraint is introduced.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G6C
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G4B
open FCP.BFSSSU2PhysicalDomainL6G6A

/-- The universal TWO-leg derivative selector for a quadratic
polynomial. Neither leg is silently discarded. -/
private theorem finitePositionPairSelector
    {I : Type*} [Fintype I] [DecidableEq I]
    (F : I → I → ℂ) (x : I → ℂ) (u : I) :
    (∑ v : I, ∑ t : I,
      F v t * ((if u = v then x t else 0) +
        (if u = t then x v else 0))) =
      (∑ t : I, F u t * x t) +
        (∑ v : I, F v u * x v) := by
  classical
  have hfirst (t : I) :
      (∑ v : I, F v t * (if u = v then x t else 0)) =
        F u t * x t := by
    simp [mul_ite]
  have hsecond (v : I) :
      (∑ t : I, F v t * (if u = t then x v else 0)) =
        F v u * x v := by
    simp [mul_ite]
  have hf :
      (∑ v : I, ∑ t : I,
        F v t * (if u = v then x t else 0)) =
          ∑ t : I, F u t * x t := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    exact hfirst t
  have hs :
      (∑ v : I, ∑ t : I,
        F v t * (if u = t then x v else 0)) =
          ∑ v : I, F v u * x v := by
    apply Finset.sum_congr rfl
    intro v _
    exact hsecond v
  calc
    _ = (∑ v : I, ∑ t : I,
          F v t * (if u = v then x t else 0)) +
        (∑ v : I, ∑ t : I,
          F v t * (if u = t then x v else 0)) := by
          simp only [mul_add, Finset.sum_add_distrib]
    _ = _ := by rw [hf, hs]

/-- The source G4B coefficient weights with the two ORIGINAL coordinate
derivative legs explicitly selected. Unlike a derivative-free model,
the two index orders are maintained independently. -/
def sourceCoefficientResponseSelected {N : ℕ}
    (M : AlgebraData N) (α β : SpinIndex)
    (p q : FermionLabel N) (x : Boson N) : ℂ :=
  ∑ u : BosonLabel N,
    ((∑ t : BosonLabel N,
      (sourceKineticWeight M α p u * sourceQuadraticWeight M β q u t -
        sourceKineticWeight M β q u * sourceQuadraticWeight M α p u t) *
          ((x t : ℝ) : ℂ)) +
     (∑ v : BosonLabel N,
      (sourceKineticWeight M α p u * sourceQuadraticWeight M β q v u -
        sourceKineticWeight M β q u * sourceQuadraticWeight M α p v u) *
          ((x v : ℝ) : ℂ)))

/-- Original pointwise source coefficient commutator, EXACTLY as defined
in G6A, equals the two explicit source position legs. -/
theorem sourceCoefficientResponsePoint_eq_selected {N : ℕ}
    (M : AlgebraData N) (α β : SpinIndex)
    (p q : FermionLabel N) (x : Boson N) :
    sourceCoefficientResponsePoint M α β p q x =
      sourceCoefficientResponseSelected M α β p q x := by
  classical
  unfold sourceCoefficientResponsePoint sourceCoefficientResponseSelected
  apply Finset.sum_congr rfl
  intro u _
  exact finitePositionPairSelector
    (fun v t : BosonLabel N =>
      sourceKineticWeight M α p u * sourceQuadraticWeight M β q v t -
        sourceKineticWeight M β q u * sourceQuadraticWeight M α p v t)
    (fun t => ((x t : ℝ) : ℂ)) u

/-- Arbitrary original real spinor weights pass through the exact
source Kronecker-selector equality without modifying their order. -/
theorem sourceAllSpinorResponsePoint_eq_selected {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (p q : FermionLabel N) (x : Boson N) :
    sourceAllSpinorResponsePoint M w p q x =
      ∑ α : SpinIndex, ∑ β : SpinIndex,
        ((w α : ℂ) * (w β : ℂ)) *
          sourceCoefficientResponseSelected M α β p q x := by
  classical
  unfold sourceAllSpinorResponsePoint
  simp_rw [sourceCoefficientResponsePoint_eq_selected]

#print axioms finitePositionPairSelector
#print axioms sourceCoefficientResponsePoint_eq_selected
#print axioms sourceAllSpinorResponsePoint_eq_selected
#check @sourceAllSpinorResponsePoint_eq_selected

end
end FCP.BFSSSU2PhysicalDomainL6G6C
