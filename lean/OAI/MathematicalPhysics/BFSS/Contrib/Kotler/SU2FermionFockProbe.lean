import Mathlib
import OAI.MathematicalPhysics.BFSS.Core
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockNorm

/-!
# BFSS fermion Stage F1 — twenty-four-mode Fock transport

Bounded source-first experiment: use the pinned upstream Laughlin/ContinuumCoulomb
creation, annihilation, adjoint and CAR lemmas. Reindex the 24-mode occupation
basis (a finite-set index) into precisely the BFSS `Fermion 2` index type.

No 2^24-by-2^24 matrices are constructed. This is NOT a complete theta family,
irreducibility, a gauge action, or a spectral theorem.
-/

namespace FCP.BFSSFermionF1
noncomputable section

open OAI.Laughlin.Fock OAI.ContinuumCoulomb.HubbardGlobal

/-- The 24-mode Fock occupation basis has exactly 2^24 vectors. -/
noncomputable def occupationIndexEquiv :
    Finset (Fin 24) ≃ Fin (2 ^ 24) :=
  (Fintype.equivFin (Finset (Fin 24))).trans
    (finCongr (by simp [Fintype.card_finset]))

/-- Exact unitary reindexing into BFSSQuantum.Fermion 2. -/
noncomputable def fockBFSSUnitary :
    FockCoordinateSpace 23 ≃ₗᵢ[ℂ] OAI.BFSSQuantum.Fermion 2 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ occupationIndexEquiv

/-- Conjugate an existing 24-mode continuous Fock operator into BFSS's exact Hilbert type. -/
noncomputable def onBFSS
    (T : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23) :
    OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2 :=
  fockBFSSUnitary.conjStarAlgEquiv T

/-- Transferred creator for one of the 24 modes. -/
noncomputable def creator (i : Fin 24) :
    OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2 :=
  onBFSS (fockOperator (create i))

/-- Transferred annihilator for the same mode. -/
noncomputable def annihilator (i : Fin 24) :
    OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2 :=
  onBFSS (fockOperator (annihilate i))

private theorem fockOperator_one :
    fockOperator (1 : Module.End ℂ (Space 23)) =
      (1 : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23) := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates 23).surjective v
  simp [fockOperator_coordinates]

private theorem fockOperator_zero :
    fockOperator (0 : Module.End ℂ (Space 23)) =
      (0 : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23) := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates 23).surjective v
  simp [fockOperator_coordinates]

private theorem fock_mixed_car (i : Fin 24) :
    fockOperator (annihilate i) * fockOperator (create i) +
      fockOperator (create i) * fockOperator (annihilate i) =
      (1 : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23) := by
  have h := congrArg
    (fun T : Module.End ℂ (Space 23) => fockOperator T)
    (OAI.Laughlin.Fock.mixed_car i i)
  simp only [ite_true, one_smul, fockOperator_add, fockOperator_mul,
    fockOperator_one] at h
  simpa only [ContinuousLinearMap.mul_def] using h

/-- A true continuous-operator CAR identity on the exact upstream BFSS Hilbert type. -/
theorem creator_annihilator_car (i : Fin 24) :
    annihilator i * creator i + creator i * annihilator i =
      (1 : OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2) := by
  have h := congrArg
    (fun T : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23 => onBFSS T)
    (fock_mixed_car i)
  simpa only [creator, annihilator, onBFSS, map_add, map_mul, map_one] using h

/-- The creator's Hilbert adjoint is exactly the corresponding annihilator. -/
theorem creator_adjoint (i : Fin 24) :
    star (creator i) = annihilator i := by
  have h : star (fockOperator (create i)) = fockOperator (annihilate i) := by
    change (fockOperator (create i)).adjoint = fockOperator (annihilate i)
    exact OAI.ContinuumCoulomb.HubbardGlobal.fockOperator_create_adjoint i
  calc
    star (creator i) =
      onBFSS (star (fockOperator (create i))) := by
        exact (map_star fockBFSSUnitary.conjStarAlgEquiv _).symm
    _ = annihilator i := by rw [h]; rfl

theorem annihilator_adjoint (i : Fin 24) :
    star (annihilator i) = creator i := by
  have h := congrArg star (creator_adjoint i)
  simpa only [star_star] using h.symm

/-- The normalized self-adjoint first Majorana from a creator/annihilator pair. -/
noncomputable def majorana0 (i : Fin 24) :
    OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2 :=
  (((Real.sqrt 2 / 2 : ℝ) : ℂ)) • (creator i + annihilator i)

theorem majorana0_selfAdjoint (i : Fin 24) :
    IsSelfAdjoint (majorana0 i) := by
  unfold majorana0
  apply IsSelfAdjoint.smul
  · simp [IsSelfAdjoint, Complex.conj_ofReal]
  · simpa only [creator_adjoint] using
      (IsSelfAdjoint.add_star_self (creator i))

private theorem fock_creator_sq (i : Fin 24) :
    fockOperator (create i) * fockOperator (create i) =
      (0 : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23) := by
  have h := congrArg
    (fun T : Module.End ℂ (Space 23) => fockOperator T)
    (OAI.Laughlin.Fock.create_sq i)
  simpa only [fockOperator_mul, fockOperator_zero,
    ContinuousLinearMap.mul_def] using h

private theorem fock_annihilator_sq (i : Fin 24) :
    fockOperator (annihilate i) * fockOperator (annihilate i) =
      (0 : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23) := by
  have h := congrArg
    (fun T : Module.End ℂ (Space 23) => fockOperator T)
    (OAI.Laughlin.Fock.annihilate_sq i)
  simpa only [fockOperator_mul, fockOperator_zero,
    ContinuousLinearMap.mul_def] using h

theorem creator_sq (i : Fin 24) :
    creator i * creator i = 0 := by
  have h := congrArg
    (fun T : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23 => onBFSS T)
    (fock_creator_sq i)
  simpa only [creator, onBFSS, map_mul, map_zero] using h

theorem annihilator_sq (i : Fin 24) :
    annihilator i * annihilator i = 0 := by
  have h := congrArg
    (fun T : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23 => onBFSS T)
    (fock_annihilator_sq i)
  simpa only [annihilator, onBFSS, map_mul, map_zero] using h

private theorem majoranaScale_sq :
    (((Real.sqrt 2 / 2 : ℝ) : ℂ)) * (((Real.sqrt 2 / 2 : ℝ) : ℂ)) =
      (1 / 2 : ℂ) := by
  have hs : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have heq : (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 2 / 2 : ℝ) = 1 / 2 :=
    (pow_two _).symm.trans hs
  have hc := congrArg (fun x : ℝ => (x : ℂ)) heq
  simpa only [Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_one] using hc

/-- The first transported Majorana squares to 1/2, hence obeys {θ,θ}=1. -/
theorem majorana0_car (i : Fin 24) :
    majorana0 i * majorana0 i + majorana0 i * majorana0 i =
      (1 : OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2) := by
  let c := creator i
  let a := annihilator i
  have hcc : c * c = 0 := creator_sq i
  have haa : a * a = 0 := annihilator_sq i
  have hca : a * c + c * a = 1 := creator_annihilator_car i
  have hsum : (c + a) * (c + a) = 1 := by
    calc
      _ = c * c + (a * c + c * a) + a * a := by noncomm_ring
      _ = 1 := by rw [hcc, haa, hca]; simp
  unfold majorana0
  change (_ • (c + a)) * (_ • (c + a)) +
    (_ • (c + a)) * (_ • (c + a)) = _
  simp only [smul_mul_smul, hsum, majoranaScale_sq]
  -- Give the scalar field explicitly to avoid an ambiguous Module instance.
  refine (add_smul (1 / 2 : ℂ) (1 / 2 : ℂ)
      (1 : OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2)).symm.trans ?_
  have hcoef : (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1 := by norm_num
  rw [hcoef, one_smul]

#print axioms fockBFSSUnitary
#print axioms creator_annihilator_car
#print axioms creator_adjoint
#print axioms majorana0_selfAdjoint
#print axioms majorana0_car

end
end FCP.BFSSFermionF1

/-!
Independent BFSS SU(2) formalization contribution by Evan T. Kotler (2026).
Research DOI: https://doi.org/10.5281/zenodo.23291242
FCP source: b60baa806dab3f0b296229a78f70e07b787544ab, experiments/openai-math-su2-concrete-potential/SU2FermionFockProbe.lean
Copyright (c) 2026 Evan T. Kotler. SPDX-License-Identifier: Apache-2.0.
Build status: integrated candidate; upstream port NOT YET independently verified.
OpenAI retains credit for the original BFSS definitions on which this work builds.
-/
