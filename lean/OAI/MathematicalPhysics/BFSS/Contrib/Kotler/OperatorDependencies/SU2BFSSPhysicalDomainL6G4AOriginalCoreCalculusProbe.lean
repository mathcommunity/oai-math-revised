import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G3OriginalChargeNormalOrderProbe
import OAI.MathematicalPhysics.BFSS.CliffordSymbols

/-!
# L6G4A — small original-source calculus for coefficient commutators

The accepted S3L3A/B/D proofs carry an unrelated concrete-Fock import
chain. Here their source-calculus arguments are faithfully generalized
to N, with the pinned upstream coordinateDerivative_multiplier reused
directly. Original SmoothCore, position and coordinateDerivative remain
literal; no replacement function space or calculus premise is supplied.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G4A
noncomputable section
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G3

abbrev BosonLabel (N : ℕ) := SpaceIndex × ColorIndex N

def sourceD {N : ℕ} (u : BosonLabel N) : SourceEnd N :=
  coordinateDerivative u.1 u.2

def sourceP {N : ℕ} (u : BosonLabel N) : SourceEnd N :=
  position u.1 u.2

private theorem sourceCoordinate_fderiv {N : ℕ}
    (v : BosonLabel N) (x z : Boson N) :
    fderiv ℝ (fun y : Boson N => (y v : ℂ)) x z = (z v : ℂ) := by
  let C : Boson N →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) v)
  have h : (fun y : Boson N => (y v : ℂ)) = C := rfl
  rw [h, ContinuousLinearMap.fderiv]
  rfl

/-- Source Heisenberg law; reuse the original upstream multiplier rule. -/
theorem sourceD_P_comm {N : ℕ} (u v : BosonLabel N) :
    sourceD u * sourceP v - sourceP v * sourceD u =
      if u = v then (1 : SourceEnd N) else 0 := by
  classical
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  have h := coordinateDerivative_multiplier u.1 u.2
    (fun y : Boson N => (coordinate v.1 v.2 y : ℂ))
    (Complex.ofRealCLM.contDiff.comp (coordinate_contDiff v.1 v.2)) f x
  change coordinateDerivative u.1 u.2 (position v.1 v.2 f) x =
    (x v : ℂ) • coordinateDerivative u.1 u.2 f x +
      (fderiv ℝ (fun y : Boson N => (y v : ℂ)) x
        (EuclideanSpace.single u 1)) • f x at h
  change coordinateDerivative u.1 u.2 (position v.1 v.2 f) x -
    (x v : ℂ) • coordinateDerivative u.1 u.2 f x =
      ((if u = v then (1 : SourceEnd N) else 0) f) x
  rw [h]
  change ((x v : ℂ) • coordinateDerivative u.1 u.2 f x +
    (fderiv ℝ (fun y : Boson N => (y v : ℂ)) x
      (EuclideanSpace.single u 1)) • f x) -
    (x v : ℂ) • coordinateDerivative u.1 u.2 f x = _
  rw [sourceCoordinate_fderiv]
  simp only [EuclideanSpace.single, PiLp.single_apply]
  by_cases huv : u = v
  · simp only [if_pos huv, if_pos huv.symm, Complex.ofReal_one,
      one_smul, Module.End.one_apply]
    abel
  · simp only [if_neg huv, if_neg (Ne.symm huv), Complex.ofReal_zero,
      zero_smul, LinearMap.zero_apply, add_zero, sub_self]
    rfl

private theorem sourceSecondDirectional_apply {N : ℕ}
    (u v : BosonLabel N) (f : SmoothCore N) (x : Boson N) :
    sourceD u (sourceD v f) x =
      fderiv ℝ (fderiv ℝ (f : Boson N → Fermion N)) x
        (EuclideanSpace.single u (1 : ℝ))
        (EuclideanSpace.single v (1 : ℝ)) := by
  let du : Boson N := EuclideanSpace.single u (1 : ℝ)
  let dv : Boson N := EuclideanSpace.single v (1 : ℝ)
  have heval :
      (fun y : Boson N => sourceD v f y) =
        fun y : Boson N => fderiv ℝ (f : Boson N → Fermion N) y dv := by
    funext y
    exact coordinateDerivative_apply v.1 v.2 f y
  have hfderiv : DifferentiableAt ℝ
      (fderiv ℝ (f : Boson N → Fermion N)) x := by
    exact ((f.contDiff.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)) x
  change fderiv ℝ (fun y : Boson N => sourceD v f y) x du = _
  rw [heval, fderiv_clm_apply hfderiv (differentiableAt_const dv)]
  simp only [fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  simpa only [du, dv]

/-- The accepted mixed-derivative argument on the literal original core. -/
theorem sourceD_D_comm {N : ℕ} (u v : BosonLabel N) :
    sourceD u * sourceD v = sourceD v * sourceD u := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change sourceD u (sourceD v f) x = sourceD v (sourceD u f) x
  rw [sourceSecondDirectional_apply, sourceSecondDirectional_apply]
  exact (f.contDiff.contDiffAt.isSymmSndFDerivAt (by norm_num))
    (EuclideanSpace.single u (1 : ℝ))
    (EuclideanSpace.single v (1 : ℝ))

/-- Original position commutation is already proved upstream. -/
theorem sourceP_P_comm {N : ℕ} (u v : BosonLabel N) :
    sourceP u * sourceP v = sourceP v * sourceP u :=
  position_commute u.1 v.1 u.2 v.2

/-- The derivative of an ordered quadratic source position product. -/
def sourcePositionPairResponse {N : ℕ} (u v t : BosonLabel N) : SourceEnd N :=
  (if u = v then sourceP t else 0) + (if u = t then sourceP v else 0)

theorem sourceD_positionPair_comm {N : ℕ} (u v t : BosonLabel N) :
    sourceD u * (sourceP v * sourceP t) -
      (sourceP v * sourceP t) * sourceD u = sourcePositionPairResponse u v t := by
  classical
  calc
    _ = (sourceD u * sourceP v - sourceP v * sourceD u) * sourceP t +
      sourceP v * (sourceD u * sourceP t - sourceP t * sourceD u) := by
        noncomm_ring
    _ = _ := by
      rw [sourceD_P_comm, sourceD_P_comm]
      unfold sourcePositionPairResponse
      split_ifs <;> simp

#print axioms OAI.BFSSQuantum.AlgebraData.coordinateDerivative_multiplier
#print axioms sourceD_P_comm
#print axioms sourceD_D_comm
#print axioms sourceP_P_comm
#print axioms sourceD_positionPair_comm

end
end FCP.BFSSSU2PhysicalDomainL6G4A
