import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4IAOneParticleContinuityProbe

/-!
# BFSS SU(2) G4-I-B1 — exact exterior-Fock vacuum and degree-one continuity

G4-I-A gave continuous SU(2) dependence of the genuine 24-orbital
matrix. Here show continuity of its action on actual 24-mode orbitals,
then of the true G4-A induced exterior action on vacuum and all
one-particle vectors, **after** the pinned normed Fock-coordinate
transport.

No topology on bare ExteriorAlgebra is assumed. The multiparticle
(2–24) wedge continuity, full Fock action on all vectors, BFSS Fermion
transport, and pinned GaugeData.fermion_continuous all remain open.
-/

namespace FCP.BFSSSU2GaugeG4IB1
noncomputable section

open scoped BigOperators
open Matrix
open OAI.BFSSQuantum
open OAI.Laughlin.Fock
open OAI.ContinuumCoulomb.HubbardGlobal
open FCP.BFSSSU2GaugeG4A FCP.BFSSSU2GaugeG4IA
open FCP.BFSSSU2GaugeG3C

/-- The very same matrix-vector action G4-A uses on all 24 orbitals,
now continuously dependent on SU(2), not an auxiliary orbital action. -/
theorem orbitalGauge_parameter_continuous (v : Orbital 23) :
    Continuous (fun g : GaugeGroup 2 => orbitalGauge g v) := by
  apply continuous_pi
  intro i
  change Continuous (fun g : GaugeGroup 2 =>
    ∑ j : Fin 24, complexOneParticleMatrix g i j * v j)
  exact continuous_finsetSum _ (fun j _ =>
    (complexOneParticleMatrix_continuous.matrix_elem i j).mul continuous_const)

/-- Embed actual exterior one-particle states into the pinned,
normed, finite-dimensional occupation coordinate Hilbert space. -/
noncomputable def fockSeedCoordinateLinear :
    Orbital 23 →ₗ[ℂ] FockCoordinateSpace 23 :=
  (fockCoordinates 23).toLinearMap.comp (ExteriorAlgebra.ι ℂ)

theorem fockSeedCoordinateLinear_apply (v : Orbital 23) :
    fockSeedCoordinateLinear v =
      fockCoordinates 23 (ExteriorAlgebra.ι ℂ v) := rfl

/-- No continuity of an untopologized exterior algebra is assumed:
the composite linear map from the actual finite-dimensional orbital
space to the normed Fock coordinates is automatically continuous. -/
theorem fockSeedCoordinateLinear_continuous :
    Continuous (fun v : Orbital 23 => fockSeedCoordinateLinear v) :=
  fockSeedCoordinateLinear.continuous_of_finiteDimensional

/-- Parameter continuity of the **actual** exterior action on every
degree-one state, measured in the pinned Fock occupation Hilbert norm. -/
theorem exteriorGauge_seedCoordinate_continuous (v : Orbital 23) :
    Continuous (fun g : GaugeGroup 2 =>
      fockCoordinates 23 (exteriorGauge g (ExteriorAlgebra.ι ℂ v))) := by
  have he (g : GaugeGroup 2) :
      fockCoordinates 23 (exteriorGauge g (ExteriorAlgebra.ι ℂ v)) =
        fockSeedCoordinateLinear (orbitalGauge g v) := by
    rw [exteriorGauge, ExteriorAlgebra.map_apply_ι]
    rfl
  have hcont :
      Continuous (fun g : GaugeGroup 2 =>
        fockSeedCoordinateLinear (orbitalGauge g v)) := by
    change Continuous ((fun w : Orbital 23 => fockSeedCoordinateLinear w) ∘
      (fun g : GaugeGroup 2 => orbitalGauge g v))
    exact fockSeedCoordinateLinear_continuous.comp
      (orbitalGauge_parameter_continuous v)
  simpa only [he] using hcont

/-- The true degree-zero exterior Fock vacuum is invariant, hence
its image under the *same pinned* coordinate transport is continuous. -/
theorem exteriorGauge_vacuum_coordinates_continuous :
    Continuous (fun g : GaugeGroup 2 =>
      fockCoordinates 23 (exteriorGauge g (1 : Space 23))) := by
  have he : (fun g : GaugeGroup 2 =>
      fockCoordinates 23 (exteriorGauge g (1 : Space 23))) =
      (fun _ : GaugeGroup 2 => fockCoordinates 23 (1 : Space 23)) := by
    funext g
    rw [exteriorGauge_vacuum]
  rw [he]
  exact continuous_const

/-- The theorem specializes to each of the actual 24 singleton
occupation basis states, using the pinned fockBasis_singleton identity. -/
theorem exteriorGauge_singleton_coordinates_continuous (i : Fin 24) :
    Continuous (fun g : GaugeGroup 2 =>
      fockCoordinates 23 (exteriorGauge g (fockBasis 23 {i}))) := by
  simpa only [fockBasis_singleton] using
    (exteriorGauge_seedCoordinate_continuous (mode i))

#print axioms orbitalGauge_parameter_continuous
#print axioms fockSeedCoordinateLinear
#print axioms fockSeedCoordinateLinear_apply
#print axioms fockSeedCoordinateLinear_continuous
#print axioms exteriorGauge_seedCoordinate_continuous
#print axioms exteriorGauge_vacuum_coordinates_continuous
#print axioms exteriorGauge_singleton_coordinates_continuous

end
end FCP.BFSSSU2GaugeG4IB1
