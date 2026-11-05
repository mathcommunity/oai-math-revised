import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4BFermionLinearTransportProbe

/-!
# BFSS SU(2) G4-C — actual operator covariance on Fermion 2

Transport the pinned exterior create/annihilate operations, through
the *accepted* Fock coordinate and BFSS isometric reindexing, onto
the exact Fermion 2 type. Prove covariance with the actual G4-B
complex-linear gauge equivalence and the G3-C unitary mode matrix.

This is NOT a proof of Fock Hilbert norm preservation. No
GaugeData.fermion is asserted, since that requires a linear ISOMETRY
equivalence, and theta covariance and joint continuity remain open.
-/

namespace FCP.BFSSSU2GaugeG4C
noncomputable section

open OAI.BFSSQuantum
open OAI.Laughlin.Fock
open OAI.ContinuumCoulomb.HubbardGlobal
open FCP.BFSSFermionF1
open FCP.BFSSSU2GaugeG3C FCP.BFSSSU2GaugeG4A FCP.BFSSSU2GaugeG4B

/-- The accepted BFSS creator is exactly the original exterior
creation operator under the qualified algebra-to-BFSS transport. -/
theorem creator_transport (i : Fin 24) (x : Space 23) :
    creator i (fockAlgebraToBFSS x) =
      fockAlgebraToBFSS (create i x) := by
  change (fockBFSSUnitary.conjStarAlgEquiv (fockOperator (create i)))
    (fockBFSSUnitary (fockCoordinates 23 x)) =
      fockBFSSUnitary (fockCoordinates 23 (create i x))
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, fockOperator_coordinates]

/-- The accepted BFSS annihilator is exactly the exterior contraction
operator under the same qualified 24-mode Fock representation. -/
theorem annihilator_transport (i : Fin 24) (x : Space 23) :
    annihilator i (fockAlgebraToBFSS x) =
      fockAlgebraToBFSS (annihilate i x) := by
  change (fockBFSSUnitary.conjStarAlgEquiv (fockOperator (annihilate i)))
    (fockBFSSUnitary (fockCoordinates 23 x)) =
      fockBFSSUnitary (fockCoordinates 23 (annihilate i x))
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, fockOperator_coordinates]

/-- Covariance of actual BFSS creators under the actual SU(2)
G4-B representation: INPUT i, OUTPUT j, coefficient U(g) j i. -/
theorem creator_fermionGauge_covariant
    (g : GaugeGroup 2) (i : Fin 24) (v : Fermion 2) :
    fermionGaugeLinearEquiv g (creator i v) =
      ∑ j : Fin 24, complexOneParticleMatrix g j i •
        creator j (fermionGaugeLinearEquiv g v) := by
  obtain ⟨x, rfl⟩ := fockAlgebraToBFSS.surjective v
  have h := congrArg fockAlgebraToBFSS (create_exteriorGauge g i x)
  simp only [map_sum, map_smul] at h
  rw [creator_transport, fermionGaugeLinearEquiv_intertwine]
  simp only [fermionGaugeLinearEquiv_intertwine, creator_transport]
  exact h

/-- Covariance of the actual BFSS annihilators, with the
INPUT/OUTPUT index convention dual to creator covariance. -/
theorem annihilator_fermionGauge_covariant
    (g : GaugeGroup 2) (i : Fin 24) (v : Fermion 2) :
    annihilator i (fermionGaugeLinearEquiv g v) =
      ∑ j : Fin 24, complexOneParticleMatrix g i j •
        fermionGaugeLinearEquiv g (annihilator j v) := by
  obtain ⟨x, rfl⟩ := fockAlgebraToBFSS.surjective v
  have h := congrArg fockAlgebraToBFSS (annihilate_exteriorGauge g i x)
  simp only [map_sum, map_smul] at h
  rw [fermionGaugeLinearEquiv_intertwine, annihilator_transport]
  simp only [annihilator_transport, fermionGaugeLinearEquiv_intertwine]
  exact h

#print axioms creator_transport
#print axioms annihilator_transport
#print axioms creator_fermionGauge_covariant
#print axioms annihilator_fermionGauge_covariant

end
end FCP.BFSSSU2GaugeG4C
