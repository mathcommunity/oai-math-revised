import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4DExteriorOccupationIsometryProbe

/-!
# BFSS SU(2) G4-E — true Fermion 2 Hilbert-space unitary group action

G4-D Gate #106 proves preservation of the exact 24-mode exterior
occupation inner product. Here the *definitionally same* pinned
Fock occupation basis and the accepted coordinate + BFSS unitary
transport convert that equation to norm preservation for the
genuine, already accepted G4-B fermionic complex-linear action.

The endpoint is an actual SU(2) group homomorphism into the
complex-linear ISOMETRIC equivalences of the exact Fermion 2 space.
48 Majorana theta covariance, joint continuity and GaugeData
are distinct future obligations, not claims of this gate.
-/

namespace FCP.BFSSSU2GaugeG4E
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open OAI.Laughlin.Fock
open OAI.ContinuumCoulomb.HubbardGlobal
open FCP.BFSSFermionF1
open FCP.BFSSSU2GaugeG4A FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2GaugeG4D

/-- The two pinned constructions use the SAME occupation basis:
fockBasis = occupationBasis definitionally. NormSq and norm^2
agree for each complex coefficient. -/
theorem fockMass_eq_occupationNormSq (x : Space 23) :
    fockMass x = occupationNormSq 23 x := by
  have hb : fockBasis 23 = occupationBasis 23 := rfl
  simp only [fockMass, occupationNormSq, hb, Complex.normSq_eq_norm_sq]

/-- SU(2) preserves the actual upstream Fock mass on every exterior
state; this is not assumed, but follows from exact G4-D isometry. -/
theorem exteriorGauge_fockMass (g : GaugeGroup 2) (x : Space 23) :
    fockMass (exteriorGauge g x) = fockMass x := by
  rw [fockMass_eq_occupationNormSq,
    fockMass_eq_occupationNormSq, exteriorGauge_occupationNormSq]

/-- Exact BFSS unitary occupation-label reindexing composes with the
pinned fockCoordinates linear equivalence to preserve squared mass. -/
theorem fockAlgebraToBFSS_norm_sq (x : Space 23) :
    ‖fockAlgebraToBFSS x‖ ^ 2 = fockMass x := by
  change ‖fockBFSSUnitary (fockCoordinates 23 x)‖ ^ 2 = fockMass x
  rw [LinearIsometryEquiv.norm_map]
  exact fockCoordinates_norm_sq x

/-- Actual full Hilbert squared-norm preservation on Fermion 2.
No nonphysical substitute Hilbert space is introduced. -/
theorem fermionGaugeLinearEquiv_norm_sq
    (g : GaugeGroup 2) (v : Fermion 2) :
    ‖fermionGaugeLinearEquiv g v‖ ^ 2 = ‖v‖ ^ 2 := by
  obtain ⟨x, rfl⟩ := fockAlgebraToBFSS.surjective v
  rw [fermionGaugeLinearEquiv_intertwine,
    fockAlgebraToBFSS_norm_sq, fockAlgebraToBFSS_norm_sq,
    exteriorGauge_fockMass]

/-- Strong norm equality, not just invertibility of the gauge action. -/
theorem fermionGaugeLinearEquiv_norm
    (g : GaugeGroup 2) (v : Fermion 2) :
    ‖fermionGaugeLinearEquiv g v‖ = ‖v‖ := by
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (fermionGaugeLinearEquiv_norm_sq g v)

/-- Actual Fermion 2 complex-linear ISOMETRIC equivalence from the
accepted exterior-algebra SU(2) action. -/
noncomputable def fermionGaugeUnitaryEquiv (g : GaugeGroup 2) :
    Fermion 2 ≃ₗᵢ[ℂ] Fermion 2 where
  toLinearEquiv := fermionGaugeLinearEquiv g
  norm_map' := fermionGaugeLinearEquiv_norm g

/-- Forgetting the norm proof returns exactly G4-B's accepted
invertible complex-linear equivalence, with no change of action. -/
theorem fermionGaugeUnitaryEquiv_toLinearEquiv (g : GaugeGroup 2) :
    (fermionGaugeUnitaryEquiv g).toLinearEquiv =
      fermionGaugeLinearEquiv g := rfl

/-- Exact SU(2) group representation by Hilbert-unitary operators,
with multiplication inherited from the certified G4-B action. -/
noncomputable def fermionGaugeUnitaryHom :
    GaugeGroup 2 →* (Fermion 2 ≃ₗᵢ[ℂ] Fermion 2) where
  toFun := fermionGaugeUnitaryEquiv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro v
    exact congrArg
      (fun T : Fermion 2 ≃ₗ[ℂ] Fermion 2 => T v)
      (map_one fermionGaugeLinearHom)
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro v
    exact congrArg
      (fun T : Fermion 2 ≃ₗ[ℂ] Fermion 2 => T v)
      (map_mul fermionGaugeLinearHom g h)

#print axioms fockMass_eq_occupationNormSq
#print axioms exteriorGauge_fockMass
#print axioms fockAlgebraToBFSS_norm_sq
#print axioms fermionGaugeLinearEquiv_norm_sq
#print axioms fermionGaugeLinearEquiv_norm
#print axioms fermionGaugeUnitaryEquiv
#print axioms fermionGaugeUnitaryEquiv_toLinearEquiv
#print axioms fermionGaugeUnitaryHom

end
end FCP.BFSSSU2GaugeG4E
