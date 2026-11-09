import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K1PhysicalSpaceCoreProbe

/-!
# BFSS SU(2) G4-K2A — nonzero Fock singlet and equivariant radial profiles

Use the accepted G4-B literal Fock-to-BFSS linear equivalence,
G4-E exact unitary fermionic action, G2-A bosonic isometry,
and G4-J six-field GaugeData to derive a true nonzero SU(2)
fermionic singlet and a family of pointwise equivariant radial
profiles on the *actual* BFSS Boson 2 / Fermion 2 spaces.

NO normalizability is asserted here: a pointwise nonzero field
need not define a nonzero FullL2 class. Finding a concrete,
nonzero, square-integrable Gauss-invariant section is a separate
future theorem with an explicit measure-theoretic proof.
-/

namespace FCP.BFSSSU2GaugeG4K2A
noncomputable section

open OAI.BFSSQuantum
open OAI.Laughlin.Fock
open FCP.BFSSSU2GaugeG2A
open FCP.BFSSSU2GaugeG4A FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2GaugeG4E FCP.BFSSSU2GaugeG4J

/-- The actual G4-B fermionic vacuum is NONZERO: it is the image
of 1 under the pinned 24-orbital Fock-to-BFSS linear equivalence.
This is not an assumed vacuum or a surrogate Fock Hilbert type. -/
theorem fermionVacuum_ne_zero :
    fermionVacuum ≠ (0 : Fermion 2) := by
  change fockAlgebraToBFSS (1 : Space 23) ≠ (0 : Fermion 2)
  intro hz
  have h1 : (1 : Space 23) = 0 := by
    apply fockAlgebraToBFSS.injective
    simpa only [map_zero] using hz
  exact one_ne_zero h1

/-- The exact G4-E unitary representation fixes this nonzero
vacuum for EVERY genuine SU(2) gauge element. -/
theorem fermionVacuum_unitary_invariant (g : GaugeGroup 2) :
    fermionGaugeUnitaryHom g fermionVacuum = fermionVacuum := by
  change fermionGaugeLinearEquiv g fermionVacuum = fermionVacuum
  exact fermionGaugeLinearEquiv_vacuum g

/-- Norm of the true G2-A bosonic gauge action is invariant. -/
theorem bosonGauge_norm (g : GaugeGroup 2) (x : Boson 2) :
    ‖bosonGauge g x‖ = ‖x‖ :=
  (bosonGauge g).norm_map x

/-- This is a POINTWISE candidate profile, not an L² construction.
It uses the true bosonic Hilbert norm and the certified fermionic
singlet. Normalizability is NOT inferred from this definition. -/
noncomputable def radialVacuumProfile (φ : ℝ → ℂ)
    (x : Boson 2) : Fermion 2 :=
  (φ ‖x‖) • fermionVacuum

/-- Every radial profile is exactly equivariant under the
literal boson and fermion actions from G2-A and G4-E. -/
theorem radialVacuumProfile_equivariant (φ : ℝ → ℂ)
    (g : GaugeGroup 2) (x : Boson 2) :
    radialVacuumProfile φ (bosonGauge g x) =
      fermionGaugeUnitaryHom g (radialVacuumProfile φ x) := by
  calc
    radialVacuumProfile φ (bosonGauge g x) =
        φ ‖x‖ • fermionVacuum := by
          simp only [radialVacuumProfile, bosonGauge_norm]
    _ = fermionGaugeUnitaryHom g (radialVacuumProfile φ x) := by
      rw [radialVacuumProfile, map_smul, fermionVacuum_unitary_invariant]

/-- The equivariance equation is stated for the ACTUAL six-field
GaugeData, not an independent or convenient replacement action. -/
theorem pairedGaugeData_radialVacuumProfile_equivariant
    (φ : ℝ → ℂ) (g : GaugeGroup 2) (x : Boson 2) :
    radialVacuumProfile φ (pairedGaugeData.boson g x) =
      pairedGaugeData.fermion g (radialVacuumProfile φ x) := by
  change radialVacuumProfile φ (bosonGauge g x) =
    fermionGaugeUnitaryHom g (radialVacuumProfile φ x)
  exact radialVacuumProfile_equivariant φ g x

/-- A radial profile with unit center coefficient is pointwise
nonzero at the origin. This does NOT yet assert nonzero L² norm. -/
theorem radialVacuumProfile_nonzero_at_origin
    (φ : ℝ → ℂ) (hφ : φ 0 = 1) :
    radialVacuumProfile φ (0 : Boson 2) ≠ 0 := by
  change φ ‖(0 : Boson 2)‖ • fermionVacuum ≠ 0
  simpa only [norm_zero, hφ, one_smul] using fermionVacuum_ne_zero

#print axioms fermionVacuum_ne_zero
#print axioms fermionVacuum_unitary_invariant
#print axioms bosonGauge_norm
#print axioms radialVacuumProfile
#print axioms radialVacuumProfile_equivariant
#print axioms pairedGaugeData_radialVacuumProfile_equivariant
#print axioms radialVacuumProfile_nonzero_at_origin

end
end FCP.BFSSSU2GaugeG4K2A
