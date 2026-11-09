import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4IB3ExteriorFockAllContinuityProbe

/-!
# BFSS SU(2) G4-I-C1 — parameter continuity on actual Fermion 2

Gate #120 showed continuous SU(2) parameter dependence on EVERY
genuine 24-mode exterior-Fock vector in the pinned occupation-
coordinate Hilbert norm.

This file transports that exact continuity through the *existing*
FCP.BFSSFermionF1.fockBFSSUnitary and the G4-B intertwining theorem
to the actual upstream BFSSQuantum.Fermion 2 Hilbert type. The map
is definitionally G4-E's genuine unitary SU(2) representation,
not a proxy linear action.

Joint continuity in (g,v), exact GaugeData assembly, and physical
spectral results are separate unproved obligations.
-/

namespace FCP.BFSSSU2GaugeG4IC1
noncomputable section

open OAI.BFSSQuantum
open OAI.Laughlin.Fock
open OAI.ContinuumCoulomb.HubbardGlobal
open FCP.BFSSFermionF1
open FCP.BFSSSU2GaugeG4A FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2GaugeG4E FCP.BFSSSU2GaugeG4IB3

/-- The exact SU(2) unitary group action constructed by G4-E has
continuous parameter dependence at EVERY fixed state in the
genuine 2^24-dimensional BFSS Fermion 2 Hilbert space.

No new topological structure, unproved isometry, or representation
equivalence is assumed: the bridge is literally the G4-B
Fock-to-BFSS equivalence and the F1 unitary occupation reindexing. -/
theorem fermionGauge_parameter_continuous (v : Fermion 2) :
    Continuous (fun g : GaugeGroup 2 => fermionGaugeUnitaryHom g v) := by
  obtain ⟨x, rfl⟩ := fockAlgebraToBFSS.surjective v
  have he :
      (fun g : GaugeGroup 2 =>
        fermionGaugeUnitaryHom g (fockAlgebraToBFSS x)) =
      (fun g : GaugeGroup 2 =>
        fockBFSSUnitary (fockCoordinates 23 (exteriorGauge g x))) := by
    funext g
    change fermionGaugeLinearEquiv g (fockAlgebraToBFSS x) =
      fockAlgebraToBFSS (exteriorGauge g x)
    exact fermionGaugeLinearEquiv_intertwine g x
  rw [he]
  exact fockBFSSUnitary.continuous.comp
    (exteriorGauge_allCoordinates_continuous x)

#print axioms fermionGauge_parameter_continuous

end
end FCP.BFSSSU2GaugeG4IC1
