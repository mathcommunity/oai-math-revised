import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4AExteriorGaugeActionProbe

/-!
# BFSS SU(2) G4-B — exact Fermion 2 complex-linear gauge transport

The certified G4-A exterior-algebra action is lifted by the *existing*
fockCoordinates 23 linear equivalence and the *accepted*
fockBFSSUnitary into OAI.BFSSQuantum.Fermion 2, dimension 2^24.

This proves an exact linear-equivalence SU(2) representation and its
intertwining relation, not an isometry. No GaugeData.fermion,
48-theta covariance, joint continuity, or spectral conclusion.
-/

namespace FCP.BFSSSU2GaugeG4B
noncomputable section

open OAI.BFSSQuantum
open OAI.Laughlin.Fock
open OAI.ContinuumCoulomb.HubbardGlobal
open FCP.BFSSFermionF1
open FCP.BFSSSU2GaugeG4A

/-- Use the same true exterior Fock space as the qualified CAR proofs. -/
private abbrev Fock23 := Space 23

/-- G4-A actually gives algebra automorphisms: the inverse is g⁻¹.
The present step equips them with the exact complex linear equivalence. -/
noncomputable def exteriorGaugeLinearEquiv (g : GaugeGroup 2) :
    Fock23 ≃ₗ[ℂ] Fock23 where
  toFun := exteriorGauge g
  invFun := exteriorGauge g⁻¹
  left_inv := by
    intro x
    exact exteriorGauge_inv g x
  right_inv := by
    intro x
    simpa only [inv_inv] using exteriorGauge_inv g⁻¹ x
  map_add' := by
    intro x y
    exact (exteriorGauge g).toLinearMap.map_add x y
  map_smul' := by
    intro c x
    exact (exteriorGauge g).toLinearMap.map_smul c x

theorem exteriorGaugeLinearEquiv_apply (g : GaugeGroup 2) (x : Fock23) :
    exteriorGaugeLinearEquiv g x = exteriorGauge g x := rfl

/-- The exact source-side Fock-coordinate linear equivalence, followed
by the independently accepted Fock-to-BFSS unitary reindexing. -/
noncomputable def fockAlgebraToBFSS :
    Fock23 ≃ₗ[ℂ] Fermion 2 :=
  (fockCoordinates 23).trans fockBFSSUnitary.toLinearEquiv

/-- A genuine complex linear equivalence on the exact BFSS fermionic
Hilbert *type*. Unitarity relative to its Hilbert norm is OPEN. -/
noncomputable def fermionGaugeLinearEquiv (g : GaugeGroup 2) :
    Fermion 2 ≃ₗ[ℂ] Fermion 2 :=
  (fockAlgebraToBFSS.symm.trans (exteriorGaugeLinearEquiv g)).trans
    fockAlgebraToBFSS

/-- Exact transported action intertwines the true G4-A exterior map. -/
theorem fermionGaugeLinearEquiv_intertwine (g : GaugeGroup 2) (x : Fock23) :
    fermionGaugeLinearEquiv g (fockAlgebraToBFSS x) =
      fockAlgebraToBFSS (exteriorGauge g x) := by
  simp only [fermionGaugeLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, exteriorGaugeLinearEquiv_apply]

/-- The same gauge action preserves the transported algebraic vacuum. -/
noncomputable def fermionVacuum : Fermion 2 :=
  fockAlgebraToBFSS (1 : Fock23)

theorem fermionGaugeLinearEquiv_vacuum (g : GaugeGroup 2) :
    fermionGaugeLinearEquiv g fermionVacuum = fermionVacuum := by
  simpa only [fermionVacuum, exteriorGauge_vacuum] using
    fermionGaugeLinearEquiv_intertwine g (1 : Fock23)

/-- Exact linear representation of SU(2) on the actual 2^24-
dimensional Fermion 2 space. This is NOT the required unitary
representation until norm preservation is kernel-proved. -/
noncomputable def fermionGaugeLinearHom :
    GaugeGroup 2 →* (Fermion 2 ≃ₗ[ℂ] Fermion 2) where
  toFun := fermionGaugeLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨x, rfl⟩ := fockAlgebraToBFSS.surjective v
    change fermionGaugeLinearEquiv 1 (fockAlgebraToBFSS x) =
      fockAlgebraToBFSS x
    rw [fermionGaugeLinearEquiv_intertwine, exteriorGauge_one]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨x, rfl⟩ := fockAlgebraToBFSS.surjective v
    rw [LinearEquiv.mul_apply,
      fermionGaugeLinearEquiv_intertwine h x,
      fermionGaugeLinearEquiv_intertwine g (exteriorGauge h x),
      fermionGaugeLinearEquiv_intertwine (g*h) x]
    exact (congrArg fockAlgebraToBFSS (exteriorGauge_mul g h x)).symm

#print axioms exteriorGaugeLinearEquiv
#print axioms exteriorGaugeLinearEquiv_apply
#print axioms fockAlgebraToBFSS
#print axioms fermionGaugeLinearEquiv
#print axioms fermionGaugeLinearEquiv_intertwine
#print axioms fermionGaugeLinearEquiv_vacuum
#print axioms fermionGaugeLinearHom

end
end FCP.BFSSSU2GaugeG4B
