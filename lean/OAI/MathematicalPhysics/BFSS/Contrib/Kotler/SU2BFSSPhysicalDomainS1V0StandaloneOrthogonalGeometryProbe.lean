import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic

/-!
S1V0 — standalone, pinned Mathlib geometric precondition for S1V.
This uses the EXACT source 48-label type Fin 24 × Fin 2 and the same
unit-weight QuadraticMap.weightedSumSquares as the accepted S1P0 source.
It does not import or substitute a different source action, and cannot
by itself qualify the original Clifford rotor equality.

RESEARCH CANDIDATE, NOT COMPILED/ACCEPTED until one strict gate passes.
-/

set_option autoImplicit false
set_option maxHeartbeats 280000

namespace FCP.BFSSS1V0
noncomputable section

abbrev Source48Label := Fin 24 × Fin 2
abbrev Source48Vector := Source48Label → ℝ

noncomputable def source48Quadratic : QuadraticForm ℝ Source48Vector :=
  QuadraticMap.weightedSumSquares ℝ
    (fun _ : Source48Label => (1 : ℝ))

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev B : Source48Vector →ₗ[ℝ] Source48Vector →ₗ[ℝ] ℝ :=
  QuadraticMap.associated Q

noncomputable def sourcePlaneComplement
    (a b v : Source48Vector) : Source48Vector :=
  v - (B a v) • a - (B b v) • b

theorem sourcePlane_decomposition (a b v : Source48Vector) :
    v = (B a v) • a + (B b v) • b +
      sourcePlaneComplement a b v := by
  dsimp [sourcePlaneComplement]
  abel

theorem sourcePlaneComplement_ortho_first
    (a b v : Source48Vector)
    (ha : Q a = 1) (_hb : Q b = 1)
    (hab : Q.IsOrtho a b) :
    Q.IsOrtho a (sourcePlaneComplement a b v) := by
  have hAA : B a a = 1 := by
    exact (QuadraticMap.associated_eq_self_apply ℝ Q a).trans ha
  have hAB : B a b = 0 := by
    exact (QuadraticMap.associated_isOrtho (Q := Q)).2 hab
  have hzero : B a (sourcePlaneComplement a b v) = 0 := by
    simp only [sourcePlaneComplement, map_sub, map_smul, smul_eq_mul,
      hAA, hAB, mul_one, mul_zero, sub_self]
  exact (QuadraticMap.associated_isOrtho (Q := Q)).1 hzero

theorem sourcePlaneComplement_ortho_second
    (a b v : Source48Vector)
    (_ha : Q a = 1) (hb : Q b = 1)
    (hab : Q.IsOrtho a b) :
    Q.IsOrtho b (sourcePlaneComplement a b v) := by
  have hBB : B b b = 1 := by
    exact (QuadraticMap.associated_eq_self_apply ℝ Q b).trans hb
  have hBA : B b a = 0 := by
    exact (QuadraticMap.associated_isOrtho (Q := Q)).2 hab.symm
  have hzero : B b (sourcePlaneComplement a b v) = 0 := by
    simp only [sourcePlaneComplement, map_sub, map_smul, smul_eq_mul,
      hBA, hBB, mul_one, mul_zero, sub_zero, sub_self]
  exact (QuadraticMap.associated_isOrtho (Q := Q)).1 hzero

#print axioms sourcePlane_decomposition
#print axioms sourcePlaneComplement_ortho_first
#print axioms sourcePlaneComplement_ortho_second

end
end FCP.BFSSS1V0
