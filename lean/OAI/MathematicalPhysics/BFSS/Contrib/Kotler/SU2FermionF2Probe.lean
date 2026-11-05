import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2FermionFockProbe

/-!
# BFSS Stage F2-A — cross-mode CAR and full 48-label self-adjoint candidate

Imports the formally accepted F1 unitary Fock transport and normalized first
Majorana (Gate #36). Extends its CAR lemmas to arbitrary mode pairs and defines
the complementary self-adjoint Majorana. The index equivalence names exactly
the 16×3 BFSS labels without allocating 2^24-square matrices.

This first F2 gate does not claim the full off-diagonal Majorana CAR or
irreducibility. These remain subsequent F2 and F3 proof obligations.
-/

namespace FCP.BFSSFermionF2
noncomputable section

open FCP.BFSSFermionF1
open OAI.Laughlin.Fock OAI.ContinuumCoulomb.HubbardGlobal

private abbrev BFSSOp :=
  OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2

private theorem fockOperator_zero :
    fockOperator (0 : Module.End ℂ (Space 23)) =
      (0 : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23) := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates 23).surjective v
  simp [fockOperator_coordinates]

private theorem fockOperator_one :
    fockOperator (1 : Module.End ℂ (Space 23)) =
      (1 : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23) := by
  ext v
  obtain ⟨x, rfl⟩ := (fockCoordinates 23).surjective v
  simp [fockOperator_coordinates]

private theorem fock_creator_creator_car (i j : Fin 24) :
    fockOperator (create i) * fockOperator (create j) +
      fockOperator (create j) * fockOperator (create i) = 0 := by
  have h := congrArg
    (fun T : Module.End ℂ (Space 23) => fockOperator T)
    (OAI.Laughlin.Fock.create_anticommute i j)
  simpa only [fockOperator_add, fockOperator_mul, fockOperator_zero,
    ContinuousLinearMap.mul_def] using h

private theorem fock_annihilator_annihilator_car (i j : Fin 24) :
    fockOperator (annihilate i) * fockOperator (annihilate j) +
      fockOperator (annihilate j) * fockOperator (annihilate i) = 0 := by
  have h := congrArg
    (fun T : Module.End ℂ (Space 23) => fockOperator T)
    (OAI.Laughlin.Fock.annihilate_anticommute i j)
  simpa only [fockOperator_add, fockOperator_mul, fockOperator_zero,
    ContinuousLinearMap.mul_def] using h

private theorem fock_mixed_car_all (i j : Fin 24) :
    fockOperator (annihilate i) * fockOperator (create j) +
      fockOperator (create j) * fockOperator (annihilate i) =
      (if i = j then (1 : ℂ) else 0) •
        (1 : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23) := by
  have h := congrArg
    (fun T : Module.End ℂ (Space 23) => fockOperator T)
    (OAI.Laughlin.Fock.mixed_car i j)
  simpa only [fockOperator_add, fockOperator_mul, fockOperator_smul,
    fockOperator_one, ContinuousLinearMap.mul_def] using h

/-- Both creators anticommute at any two of the 24 modes. -/
theorem creator_creator_car (i j : Fin 24) :
    creator i * creator j + creator j * creator i = (0 : BFSSOp) := by
  have h := congrArg
    (fun T : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23 => onBFSS T)
    (fock_creator_creator_car i j)
  simpa only [creator, onBFSS, map_add, map_mul, map_zero] using h

/-- Both annihilators anticommute at any two of the 24 modes. -/
theorem annihilator_annihilator_car (i j : Fin 24) :
    annihilator i * annihilator j + annihilator j * annihilator i =
      (0 : BFSSOp) := by
  have h := congrArg
    (fun T : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23 => onBFSS T)
    (fock_annihilator_annihilator_car i j)
  simpa only [annihilator, onBFSS, map_add, map_mul, map_zero] using h

/-- Full mixed creation/annihilation relation, including off-diagonal modes. -/
theorem annihilator_creator_car (i j : Fin 24) :
    annihilator i * creator j + creator j * annihilator i =
      (if i = j then (1 : ℂ) else 0) • (1 : BFSSOp) := by
  have h := congrArg
    (fun T : FockCoordinateSpace 23 →L[ℂ] FockCoordinateSpace 23 => onBFSS T)
    (fock_mixed_car_all i j)
  simpa only [annihilator, creator, onBFSS, map_add, map_mul,
    map_smul, map_one] using h

/-- The imaginary self-adjoint Majorana component for each complex Fock mode. -/
noncomputable def majorana1 (i : Fin 24) : BFSSOp :=
  (((Real.sqrt 2 / 2 : ℝ) : ℂ)) •
    ((Complex.I • creator i) + star (Complex.I • creator i))

theorem majorana1_selfAdjoint (i : Fin 24) :
    IsSelfAdjoint (majorana1 i) := by
  unfold majorana1
  apply IsSelfAdjoint.smul
  · simp [IsSelfAdjoint, Complex.conj_ofReal]
  · exact IsSelfAdjoint.add_star_self (Complex.I • creator i)

/-- Dimension-preserving bijection between all BFSS fermion labels and
twenty-four Fock modes with two Majoranas per mode. -/
noncomputable def thetaLabelEquiv :
    (OAI.BFSSQuantum.SpinIndex × OAI.BFSSQuantum.ColorIndex 2) ≃
      (Fin 24 × Fin 2) :=
  (Fintype.equivFin _).trans
    ((finCongr (by
        norm_num [Fintype.card_prod, OAI.BFSSQuantum.SpinIndex,
          OAI.BFSSQuantum.ColorIndex, OAI.BFSSQuantum.colorDim])).trans
      (Fintype.equivFin _).symm)

/-- The complete index family is defined, without yet claiming all its CAR. -/
noncomputable def majoranaCandidate (p : Fin 24 × Fin 2) : BFSSOp :=
  if p.2 = 0 then majorana0 p.1 else majorana1 p.1

theorem majoranaCandidate_selfAdjoint (p : Fin 24 × Fin 2) :
    IsSelfAdjoint (majoranaCandidate p) := by
  unfold majoranaCandidate
  split_ifs
  · exact majorana0_selfAdjoint p.1
  · exact majorana1_selfAdjoint p.1

/-- Exact upstream theta field signature, with self-adjointness proved.
The CAR and irreducibility fields remain distinct obligations. -/
noncomputable def thetaCandidate
    (α : OAI.BFSSQuantum.SpinIndex)
    (A : OAI.BFSSQuantum.ColorIndex 2) : BFSSOp :=
  majoranaCandidate (thetaLabelEquiv (α, A))

theorem thetaCandidate_selfAdjoint
    (α : OAI.BFSSQuantum.SpinIndex)
    (A : OAI.BFSSQuantum.ColorIndex 2) :
    IsSelfAdjoint (thetaCandidate α A) :=
  majoranaCandidate_selfAdjoint _

#print axioms creator_creator_car
#print axioms annihilator_annihilator_car
#print axioms annihilator_creator_car
#print axioms majorana1_selfAdjoint
#print axioms thetaLabelEquiv
#print axioms thetaCandidate_selfAdjoint

end
end FCP.BFSSFermionF2

/-!
Independent BFSS SU(2) formalization contribution by Evan T. Kotler (2026).
Research DOI: https://doi.org/10.5281/zenodo.23291242
FCP source: b60baa806dab3f0b296229a78f70e07b787544ab, experiments/openai-math-su2-concrete-potential/SU2FermionF2Probe.lean
Copyright (c) 2026 Evan T. Kotler. SPDX-License-Identifier: Apache-2.0.
Build status: integrated candidate; upstream port NOT YET independently verified.
OpenAI retains credit for the original BFSS definitions on which this work builds.
-/
