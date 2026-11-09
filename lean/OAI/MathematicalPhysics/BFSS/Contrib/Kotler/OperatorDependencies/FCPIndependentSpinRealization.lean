import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Independently supplied Hermitian real Clifford actions restrict to genuine
Hilbert-unitary actions of the actual Mathlib Spin subgroup.

The all-Clifford identity uses REVERSION, not Clifford star. Clifford star
equals reversion on Spin elements because those elements are even.
No Fock space, intertwiner, source gauge action, irreducibility, or phase choice
occurs in these definitions or proofs.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace FCP.IndependentSpinRealization
noncomputable section

variable {M E : Type*} [AddCommGroup M] [Module ℝ M]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

variable (Q : QuadraticForm ℝ M)
variable (rho : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ E)

/-- The correct all-Clifford Hilbert adjoint rule. -/
theorem reversion_adjoint
    (hHermitian : ∀ v : M, (rho (CliffordAlgebra.ι Q v)).IsSymmetric)
    (x : CliffordAlgebra Q) :
    rho (CliffordAlgebra.reverse x) = star (rho x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      rw [CliffordAlgebra.reverse.commutes, rho.commutes]
      change r • (1 : Module.End ℂ E) = star (r • (1 : Module.End ℂ E))
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r (1 : Module.End ℂ E)]
      simp
  | ι v =>
      rw [CliffordAlgebra.reverse_ι]
      exact (hHermitian v).adjoint_eq.symm
  | mul a b ha hb =>
      simp only [CliffordAlgebra.reverse.map_mul, map_mul, star_mul, ha, hb]
  | add a b ha hb =>
      simp only [map_add, star_add, ha, hb]

/-- Clifford star is compatible with the Hilbert adjoint on genuine Spin
elements; no assertion about odd generators is used. -/
theorem spin_star_adjoint
    (hHermitian : ∀ v : M, (rho (CliffordAlgebra.ι Q v)).IsSymmetric)
    (s : spinGroup Q) :
    rho (star (s : CliffordAlgebra Q)) = star (rho (s : CliffordAlgebra Q)) := by
  rw [CliffordAlgebra.star_def, spinGroup.involute_eq s.property]
  exact reversion_adjoint Q rho hHermitian s

theorem spin_adjoint_mul_self
    (hHermitian : ∀ v : M, (rho (CliffordAlgebra.ι Q v)).IsSymmetric)
    (s : spinGroup Q) :
    star (rho (s : CliffordAlgebra Q)) * rho (s : CliffordAlgebra Q) = 1 := by
  rw [← spin_star_adjoint Q rho hHermitian s, ← map_mul,
    spinGroup.star_mul_self_of_mem s.property, map_one]

theorem spin_mul_adjoint_self
    (hHermitian : ∀ v : M, (rho (CliffordAlgebra.ι Q v)).IsSymmetric)
    (s : spinGroup Q) :
    rho (s : CliffordAlgebra Q) * star (rho (s : CliffordAlgebra Q)) = 1 := by
  rw [← spin_star_adjoint Q rho hHermitian s, ← map_mul,
    spinGroup.mul_star_self_of_mem s.property, map_one]

/-- The inverse comes from the independently given Clifford action on the
actual Spin inverse. It is not defined by conjugating a Fock action. -/
def spinLinearEquiv (s : spinGroup Q) : E ≃ₗ[ℂ] E where
  toLinearMap := rho (s : CliffordAlgebra Q)
  invFun := rho (s⁻¹ : spinGroup Q)
  left_inv w := by
    change (rho (s⁻¹ : spinGroup Q) * rho (s : CliffordAlgebra Q)) w = w
    rw [← map_mul]
    change rho (star (s : CliffordAlgebra Q) * (s : CliffordAlgebra Q)) w = w
    rw [spinGroup.star_mul_self_of_mem s.property, map_one]
    rfl
  right_inv w := by
    change (rho (s : CliffordAlgebra Q) * rho (s⁻¹ : spinGroup Q)) w = w
    rw [← map_mul]
    change rho ((s : CliffordAlgebra Q) * star (s : CliffordAlgebra Q)) w = w
    rw [spinGroup.mul_star_self_of_mem s.property, map_one]
    rfl

def spinLinearHom : spinGroup Q →* (E ≃ₗ[ℂ] E) where
  toFun := spinLinearEquiv Q rho
  map_one' := by
    apply LinearEquiv.ext
    intro w
    change rho (1 : CliffordAlgebra Q) w = w
    rw [map_one]
    rfl
  map_mul' s t := by
    apply LinearEquiv.ext
    intro w
    change rho ((s : CliffordAlgebra Q) * (t : CliffordAlgebra Q)) w =
      rho (s : CliffordAlgebra Q) (rho (t : CliffordAlgebra Q) w)
    rw [map_mul]
    rfl

theorem spin_inner_map_map
    (hHermitian : ∀ v : M, (rho (CliffordAlgebra.ι Q v)).IsSymmetric)
    (s : spinGroup Q) (x y : E) :
    inner ℂ (rho (s : CliffordAlgebra Q) x) (rho (s : CliffordAlgebra Q) y) =
      inner ℂ x y := by
  rw [← LinearMap.adjoint_inner_right]
  change inner ℂ x ((star (rho (s : CliffordAlgebra Q)) *
    rho (s : CliffordAlgebra Q)) y) = inner ℂ x y
  rw [spin_adjoint_mul_self Q rho hHermitian s]
  rfl

def spinUnitaryEquiv
    (hHermitian : ∀ v : M, (rho (CliffordAlgebra.ι Q v)).IsSymmetric)
    (s : spinGroup Q) : E ≃ₗᵢ[ℂ] E :=
  (spinLinearEquiv Q rho s).isometryOfInner
    (spin_inner_map_map Q rho hHermitian s)

def spinUnitaryHom
    (hHermitian : ∀ v : M, (rho (CliffordAlgebra.ι Q v)).IsSymmetric) :
    spinGroup Q →* (E ≃ₗᵢ[ℂ] E) where
  toFun := spinUnitaryEquiv Q rho hHermitian
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro w
    exact DFunLike.congr_fun (map_one (spinLinearHom Q rho)) w
  map_mul' s t := by
    apply LinearIsometryEquiv.ext
    intro w
    exact DFunLike.congr_fun (map_mul (spinLinearHom Q rho) s t) w

omit [FiniteDimensional ℂ E] in
/-- Covariance follows by applying the independent algebra action to an
actual Clifford conjugation identity. This theorem does not use any J. -/
theorem spin_covariance_of_clifford_conjugation
    (s : spinGroup Q) (v v' : M)
    (hconj : (s : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
      star (s : CliffordAlgebra Q) = CliffordAlgebra.ι Q v') (w : E) :
    spinLinearEquiv Q rho s (rho (CliffordAlgebra.ι Q v) w) =
      rho (CliffordAlgebra.ι Q v') (spinLinearEquiv Q rho s w) := by
  have h := congrArg rho hconj
  simp only [map_mul] at h
  have hinv : rho (star (s : CliffordAlgebra Q)) *
      rho (s : CliffordAlgebra Q) = 1 := by
    rw [← map_mul, spinGroup.star_mul_self_of_mem s.property, map_one]
  have hright : rho (s : CliffordAlgebra Q) * rho (CliffordAlgebra.ι Q v) =
      rho (CliffordAlgebra.ι Q v') * rho (s : CliffordAlgebra Q) := by
    calc
      rho (s : CliffordAlgebra Q) * rho (CliffordAlgebra.ι Q v) =
          (rho (s : CliffordAlgebra Q) * rho (CliffordAlgebra.ι Q v)) *
            (rho (star (s : CliffordAlgebra Q)) *
              rho (s : CliffordAlgebra Q)) := by rw [hinv, mul_one]
      _ = (rho (s : CliffordAlgebra Q) * rho (CliffordAlgebra.ι Q v) *
            rho (star (s : CliffordAlgebra Q))) * rho (s : CliffordAlgebra Q) :=
              (mul_assoc _ _ _).symm
      _ = _ := congrArg (fun a => a * rho (s : CliffordAlgebra Q)) h
  exact DFunLike.congr_fun hright w

#print axioms reversion_adjoint
#print axioms spin_star_adjoint
#print axioms spin_adjoint_mul_self
#print axioms spin_mul_adjoint_self
#print axioms spinLinearHom
#print axioms spinUnitaryHom
#print axioms spin_covariance_of_clifford_conjugation

end
end FCP.IndependentSpinRealization
