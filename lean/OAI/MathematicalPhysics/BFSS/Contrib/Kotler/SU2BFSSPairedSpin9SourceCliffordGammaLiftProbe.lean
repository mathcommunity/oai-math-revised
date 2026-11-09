import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2RealGammaProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
K1D18V10C — true nine-source-vector real Clifford quadratic
identity and universal gamma representation into original
BFSS 16-real-spinor matrix algebra.

This is the first constructive ingredient for a possible group
Spin(9) → GL(16,ℝ), not itself a Spin(9) group homomorphism.
It uses exactly the accepted FCP.BFSSGamma9.gamma signed
permutations from SU2RealGammaProbe (no alternate gamma model).

No group restriction, source Spin9 topology, SO(48) reindexing,
Fock action or BFSS spectral theorem is claimed.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSGamma9
open Matrix

/-- The positive unit-weight quadratic form on the actual nine
source spatial indices, not the original 48 fermion labels. -/
noncomputable def source9Quadratic : QuadraticForm ℝ (SpaceIndex → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ
    (fun _ : SpaceIndex => (1 : ℝ))

/-- The exact accepted nine real gamma matrices extended linearly
to arbitrary vectors on the actual nine-index source carrier. -/
noncomputable def gammaNineRealLinear :
    (SpaceIndex → ℝ) →ₗ[ℝ] GammaMatrix where
  toFun v := ∑ i : SpaceIndex, (v i) • gamma i
  map_add' := by
    intro v w
    change (∑ i : SpaceIndex, (v i + w i) • gamma i) =
      (∑ i : SpaceIndex, (v i) • gamma i) +
        ∑ i : SpaceIndex, (w i) • gamma i
    calc
      (∑ i : SpaceIndex, (v i + w i) • gamma i) =
          ∑ i : SpaceIndex, ((v i) • gamma i + (w i) • gamma i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact add_smul (v i) (w i) (gamma i)
      _ = _ := Finset.sum_add_distrib
  map_smul' := by
    intro c v
    simp only [Pi.smul_apply, RingHom.id_apply,
      Finset.smul_sum, smul_smul, smul_eq_mul]

/-- The exact nine-source quadratic form is the finite
Euclidean sum of squares. -/
theorem source9Quadratic_eq_dot (v : SpaceIndex → ℝ) :
    source9Quadratic v = dotProduct v v := by
  simp [source9Quadratic, QuadraticMap.weightedSumSquares_apply,
    dotProduct]

/-- The accepted nine gammas obey the *all-vector* real
Clifford square law, not merely nine basis anticommutators. -/
theorem gammaNineRealLinear_sq (v : SpaceIndex → ℝ) :
    gammaNineRealLinear v * gammaNineRealLinear v =
      (source9Quadratic v) • (1 : GammaMatrix) := by
  classical
  have hdiag (i : SpaceIndex) :
      gamma i * gamma i = (1 : GammaMatrix) := by
    have h : gamma i * gamma i + gamma i * gamma i =
        (1 : GammaMatrix) + (1 : GammaMatrix) := by
      simpa only [eq_self, ite_true, two_smul] using
        (gamma_clifford i i)
    ext a b
    have hab := congrArg (fun M : GammaMatrix => M a b) h
    simp only [Matrix.add_apply] at hab
    linarith
  have hanti (i j : SpaceIndex) (hij : i ≠ j) :
      gamma i * gamma j + gamma j * gamma i = 0 := by
    simpa [hij] using (gamma_clifford i j)
  let X : SpaceIndex → GammaMatrix := fun i => (v i) • gamma i
  have hdiagX (i : SpaceIndex) :
      X i * X i = (v i * v i) • (1 : GammaMatrix) := by
    change ((v i) • gamma i) * ((v i) • gamma i) =
      (v i * v i) • (1 : GammaMatrix)
    rw [smul_mul_smul, hdiag i]
  have hcrossX (i j : SpaceIndex) (hij : i ≠ j) :
      X i * X j + X j * X i = 0 := by
    change ((v i) • gamma i) * ((v j) • gamma j) +
      ((v j) • gamma j) * ((v i) • gamma i) = 0
    calc
      ((v i) • gamma i) * ((v j) • gamma j) +
          ((v j) • gamma j) * ((v i) • gamma i) =
        (v i * v j) • (gamma i * gamma j) +
          (v i * v j) • (gamma j * gamma i) := by
            rw [smul_mul_smul, smul_mul_smul,
              mul_comm (v j) (v i)]
      _ = (v i * v j) •
          (gamma i * gamma j + gamma j * gamma i) :=
        (smul_add (v i * v j) (gamma i * gamma j)
          (gamma j * gamma i)).symm
      _ = 0 := by
        rw [hanti i j hij]
        exact smul_zero (v i * v j)
  have hsum (s : Finset SpaceIndex) :
      (∑ i ∈ s, X i) * (∑ i ∈ s, X i) =
        (∑ i ∈ s, v i * v i) • (1 : GammaMatrix) := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, zero_mul]
        exact (zero_smul ℝ (1 : GammaMatrix)).symm
    | @insert i t hi ih =>
        have hcrossSum :
            X i * (∑ j ∈ t, X j) +
              (∑ j ∈ t, X j) * X i = 0 := by
          rw [Finset.mul_sum, Finset.sum_mul,
            ← Finset.sum_add_distrib]
          apply Finset.sum_eq_zero
          intro j hj
          have hij : i ≠ j := by
            intro heq
            subst j
            exact hi hj
          exact hcrossX i j hij
        simp only [Finset.sum_insert hi]
        calc
          (X i + ∑ j ∈ t, X j) *
              (X i + ∑ j ∈ t, X j) =
            X i * X i +
              (∑ j ∈ t, X j) * (∑ j ∈ t, X j) +
              (X i * (∑ j ∈ t, X j) +
                (∑ j ∈ t, X j) * X i) := by
                  noncomm_ring
          _ = (v i * v i) • (1 : GammaMatrix) +
                (∑ j ∈ t, v j * v j) • (1 : GammaMatrix) := by
                  rw [hcrossSum, add_zero, hdiagX i, ih]
          _ = (v i * v i + ∑ j ∈ t, v j * v j) •
                (1 : GammaMatrix) :=
                  (add_smul (v i * v i)
                    (∑ j ∈ t, v j * v j) (1 : GammaMatrix)).symm
  calc
    gammaNineRealLinear v * gammaNineRealLinear v =
        (∑ i : SpaceIndex, X i) * (∑ i : SpaceIndex, X i) := by rfl
    _ = (∑ i : SpaceIndex, v i * v i) • (1 : GammaMatrix) :=
      hsum Finset.univ
    _ = (source9Quadratic v) • (1 : GammaMatrix) := by
      rw [source9Quadratic_eq_dot]
      rfl

/-- Algebraic Clifford universal property realized by the source
gamma matrices. This map is not yet restricted to Spin(9). -/
noncomputable def source9GammaCliffordAlgHom :
    CliffordAlgebra source9Quadratic →ₐ[ℝ] GammaMatrix := by
  let f : (SpaceIndex → ℝ) →ₗ[ℝ] GammaMatrix := gammaNineRealLinear
  have hq (v : SpaceIndex → ℝ) :
      f v * f v = algebraMap ℝ GammaMatrix (source9Quadratic v) := by
    change gammaNineRealLinear v * gammaNineRealLinear v =
      algebraMap ℝ GammaMatrix (source9Quadratic v)
    calc
      gammaNineRealLinear v * gammaNineRealLinear v =
          (source9Quadratic v) • (1 : GammaMatrix) :=
        gammaNineRealLinear_sq v
      _ = algebraMap ℝ GammaMatrix (source9Quadratic v) := by
        exact
          (Algebra.algebraMap_eq_smul_one (source9Quadratic v) :
            algebraMap ℝ GammaMatrix (source9Quadratic v) =
              (source9Quadratic v) • (1 : GammaMatrix)).symm
  exact CliffordAlgebra.lift source9Quadratic ⟨f, hq⟩

/-- The actual universal Clifford representation recovers the
source matrix-gamma real-linear combination on each nine-vector. -/
theorem source9GammaCliffordAlgHom_generator (v : SpaceIndex → ℝ) :
    source9GammaCliffordAlgHom
      (CliffordAlgebra.ι source9Quadratic v) =
        gammaNineRealLinear v := by
  unfold source9GammaCliffordAlgHom
  rw [CliffordAlgebra.lift_ι_apply]

#print axioms source9Quadratic_eq_dot
#print axioms gammaNineRealLinear_sq
#print axioms source9GammaCliffordAlgHom
#print axioms source9GammaCliffordAlgHom_generator

end
end FCP.BFSSPairedSpin9Clifford
