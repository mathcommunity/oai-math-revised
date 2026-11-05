import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.Complex.Basic

/-!
Construct the independent Clifford action from actual operators.
This generalizes the accepted source-only finite CAR contraction to
an arbitrary algebra B. No source Fock module occurs in this file.
The real coordinate form is literally weightedSumSquares with unit weights.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace FCP.IndependentM3JAction
noncomputable section

theorem finite_weighted_clifford_square
    {R B I : Type*} [CommRing R] [Ring B] [Algebra R B]
    (s : Finset I) (c : I → R) (gamma : I → B)
    (hdiag : ∀ i, gamma i * gamma i = 1)
    (hanti : ∀ i j, i ≠ j → gamma i * gamma j + gamma j * gamma i = 0) :
    (∑ i ∈ s, c i • gamma i) * (∑ i ∈ s, c i • gamma i) =
      (∑ i ∈ s, c i * c i) • (1 : B) := by
  classical
  let X := fun i => c i • gamma i
  have hdiagX (i : I) : X i * X i = (c i * c i) • (1 : B) := by
    change (c i • gamma i) * (c i • gamma i) = _
    rw [smul_mul_smul, hdiag]
  have hcrossX (i j : I) (hij : i ≠ j) : X i * X j + X j * X i = 0 := by
    change (c i • gamma i) * (c j • gamma j) +
      (c j • gamma j) * (c i • gamma i) = 0
    rw [smul_mul_smul, smul_mul_smul, mul_comm (c j) (c i),
      ← smul_add, hanti i j hij, smul_zero]
  have hsum (t : Finset I) :
      (∑ i ∈ t, X i) * (∑ i ∈ t, X i) =
        (∑ i ∈ t, c i * c i) • (1 : B) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      have hcross : X i * (∑ j ∈ t, X j) + (∑ j ∈ t, X j) * X i = 0 := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro j hj
        apply hcrossX
        intro hij
        exact hi (hij ▸ hj)
      simp only [Finset.sum_insert hi]
      calc
        (X i + ∑ j ∈ t, X j) * (X i + ∑ j ∈ t, X j) =
          X i * X i + (∑ j ∈ t, X j) * (∑ j ∈ t, X j) +
            (X i * (∑ j ∈ t, X j) + (∑ j ∈ t, X j) * X i) := by noncomm_ring
        _ = (c i * c i) • (1 : B) + (∑ j ∈ t, c j * c j) • (1 : B) := by
          rw [hcross, add_zero, hdiagX, ih]
        _ = _ := (add_smul _ _ (1 : B)).symm
  exact hsum s

variable {R S I B : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [Fintype I]
variable [Ring B] [Algebra S B] [Algebra R B] [IsScalarTower R S B]

def coordinateQuadratic : QuadraticForm R (I → R) :=
  QuadraticMap.weightedSumSquares R (fun _ : I => (1 : R))

def independentGammaReal (gamma : I → B) : (I → R) →ₗ[R] B :=
  (Pi.basisFun R I).constr R gamma

theorem independentGammaReal_axis [DecidableEq I] (gamma : I → B) (i : I) :
    independentGammaReal (R := R) gamma (Pi.single i (1 : R)) = gamma i := by
  simpa only [independentGammaReal, Pi.basisFun_apply] using
    (Pi.basisFun R I).constr_basis R gamma i

theorem independentGammaReal_square
    (gamma : I → B)
    (hdiag : ∀ i, gamma i * gamma i = 1)
    (hanti : ∀ i j, i ≠ j → gamma i * gamma j + gamma j * gamma i = 0)
    (v : I → R) :
    independentGammaReal gamma v * independentGammaReal gamma v =
      algebraMap R B (coordinateQuadratic v) := by
  have hg : independentGammaReal gamma v = ∑ i, v i • gamma i := by
    simp only [independentGammaReal, Module.Basis.constr_apply_fintype,
      Pi.basisFun_equivFun, LinearEquiv.refl_apply]
  rw [hg, finite_weighted_clifford_square Finset.univ v gamma hdiag hanti]
  simp only [coordinateQuadratic, QuadraticMap.weightedSumSquares_apply,
    one_smul, Algebra.algebraMap_eq_smul_one]

def independentRealCliffordAction
    (gamma : I → B)
    (hdiag : ∀ i, gamma i * gamma i = 1)
    (hanti : ∀ i j, i ≠ j → gamma i * gamma j + gamma j * gamma i = 0) :
    CliffordAlgebra (coordinateQuadratic (R := R) (I := I)) →ₐ[R] B :=
  CliffordAlgebra.lift _ ⟨independentGammaReal gamma,
    independentGammaReal_square gamma hdiag hanti⟩

theorem independentRealCliffordAction_generator
    (gamma : I → B) (hdiag) (hanti) (v : I → R) :
    independentRealCliffordAction gamma hdiag hanti (CliffordAlgebra.ι _ v) =
      independentGammaReal gamma v :=
  CliffordAlgebra.lift_ι_apply _ _ v

open scoped TensorProduct

variable [Invertible (2 : R)]

/-- The independent complex algebra action is CONSTRUCTED, not assumed. -/
def independentComplexCliffordAction
    (gamma : I → B)
    (hdiag : ∀ i, gamma i * gamma i = 1)
    (hanti : ∀ i j, i ≠ j → gamma i * gamma j + gamma j * gamma i = 0) :
    CliffordAlgebra ((coordinateQuadratic (R := R) (I := I)).baseChange S) →ₐ[S] B :=
  (Algebra.TensorProduct.lift (Algebra.ofId S B)
    (independentRealCliffordAction gamma hdiag hanti)
    (fun _ _ => Algebra.commutes _ _)).comp
      (CliffordAlgebra.toBaseChange S _)

theorem independentComplexCliffordAction_generator
    (gamma : I → B) (hdiag) (hanti) (v : I → R) :
    independentComplexCliffordAction (R := R) (S := S) gamma hdiag hanti
      (CliffordAlgebra.ι _ ((1 : S) ⊗ₜ[R] v)) = independentGammaReal gamma v := by
  have hpure :
      (Algebra.TensorProduct.lift (Algebra.ofId S B)
        (independentRealCliffordAction gamma hdiag hanti)
        (fun _ _ => Algebra.commutes _ _))
          ((1 : S) ⊗ₜ[R] (CliffordAlgebra.ι (coordinateQuadratic (R := R) (I := I))) v) =
      independentGammaReal gamma v := by
    change (Algebra.ofId S B) (1 : S) *
      independentRealCliffordAction gamma hdiag hanti (CliffordAlgebra.ι _ v) = _
    simpa only [map_one, one_mul] using
      independentRealCliffordAction_generator gamma hdiag hanti v
  simpa only [independentComplexCliffordAction, AlgHom.coe_comp,
    Function.comp_apply, CliffordAlgebra.toBaseChange_ι] using hpure

#print axioms finite_weighted_clifford_square
#print axioms independentGammaReal_axis
#print axioms independentGammaReal_square
#print axioms independentRealCliffordAction
#print axioms independentComplexCliffordAction
#print axioms independentComplexCliffordAction_generator

end
end FCP.IndependentM3JAction
