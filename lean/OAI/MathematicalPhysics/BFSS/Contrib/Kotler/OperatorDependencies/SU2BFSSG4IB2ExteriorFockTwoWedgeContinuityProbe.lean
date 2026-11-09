import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4IB1ExteriorFockSeedContinuityProbe

/-!
# BFSS SU(2) G4-I-B2 — exact parameter continuity on two-particle wedges

The accepted G4-I-A/G4-I-B1 matrix and one-particle continuity
results extend here to a **genuine** two-particle Fock state.

We expand the actual exterior-algebra product of two orbital
vectors into a finite polynomial, taking values in the *pinned*
normed occupation-coordinate Hilbert space via fockCoordinates 23.

This does not claim higher-degree continuity, arbitrary Fock
vector continuity, fermion_continuous or complete GaugeData.
-/

namespace FCP.BFSSSU2GaugeG4IB2
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open OAI.Laughlin.Fock
open OAI.ContinuumCoulomb.HubbardGlobal
open FCP.BFSSSU2GaugeG4A FCP.BFSSSU2GaugeG4IB1

/-- The actual pinned occupation-coordinate image of a fixed
two-orbital wedge; not a new or substituted Fock realization. -/
noncomputable def wedgePairCoordinate (i j : Fin 24) :
    FockCoordinateSpace 23 :=
  fockCoordinates 23
    (ExteriorAlgebra.ι ℂ (mode i) * ExteriorAlgebra.ι ℂ (mode j))

/-- A genuine two-particle exterior state has a finite coordinate
polynomial in the two orbital coefficient vectors. -/
theorem wedgePairCoordinate_expansion (u v : Orbital 23) :
    fockCoordinates 23
      (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v) =
    ∑ i : Fin 24, ∑ j : Fin 24,
      (u i * v j) • wedgePairCoordinate i j := by
  have hu :
      ExteriorAlgebra.ι ℂ u =
        ∑ i : Fin 24, u i • ExteriorAlgebra.ι ℂ (mode i) := by
    simpa only [map_sum, map_smul] using
      congrArg (ExteriorAlgebra.ι ℂ) (orbital_sum_modes 23 u)
  have hv :
      ExteriorAlgebra.ι ℂ v =
        ∑ j : Fin 24, v j • ExteriorAlgebra.ι ℂ (mode j) := by
    simpa only [map_sum, map_smul] using
      congrArg (ExteriorAlgebra.ι ℂ) (orbital_sum_modes 23 v)
  calc
    fockCoordinates 23 (ExteriorAlgebra.ι ℂ u *
        ExteriorAlgebra.ι ℂ v) =
      fockCoordinates 23
        ((∑ i : Fin 24, u i • ExteriorAlgebra.ι ℂ (mode i)) *
        (∑ j : Fin 24, v j • ExteriorAlgebra.ι ℂ (mode j))) := by
          rw [hu, hv]
    _ = ∑ i : Fin 24, ∑ j : Fin 24,
          (u i * v j) • wedgePairCoordinate i j := by
          calc
            _ = ∑ j : Fin 24, ∑ i : Fin 24,
                  (v j * u i) • wedgePairCoordinate i j := by
                    simp only [Finset.sum_mul, Finset.mul_sum,
                      smul_mul_assoc, mul_smul_comm, map_sum,
                      map_smul, Finset.smul_sum, smul_smul,
                      wedgePairCoordinate]
            _ = ∑ i : Fin 24, ∑ j : Fin 24,
                  (u i * v j) • wedgePairCoordinate i j := by
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro i _
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [mul_comm (v j) (u i)]

/-- Each actual orbital coordinate is continuously dependent on SU(2)
by the already compiled G4-I-B1 one-particle theorem. -/
private theorem orbitalGauge_component_continuous
    (w : Orbital 23) (i : Fin 24) :
    Continuous (fun g : GaugeGroup 2 => (orbitalGauge g w) i) :=
  (continuous_apply i).comp (orbitalGauge_parameter_continuous w)

/-- The genuine G4-A exterior-algebra gauge action is continuously
parameter-dependent on *every* two-particle wedge (not just basis
wedges), in the actual occupation-coordinate Hilbert norm. -/
theorem exteriorGauge_wedgePair_coordinates_continuous
    (u v : Orbital 23) :
    Continuous (fun g : GaugeGroup 2 =>
      fockCoordinates 23
        (exteriorGauge g
          (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v))) := by
  have hpoly : Continuous (fun g : GaugeGroup 2 =>
      ∑ i : Fin 24, ∑ j : Fin 24,
        ((orbitalGauge g u) i * (orbitalGauge g v) j) •
          wedgePairCoordinate i j) := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact ((orbitalGauge_component_continuous u i).mul
      (orbitalGauge_component_continuous v j)).smul continuous_const
  have he :
      (fun g : GaugeGroup 2 =>
        fockCoordinates 23
          (exteriorGauge g
            (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v))) =
      (fun g : GaugeGroup 2 =>
        ∑ i : Fin 24, ∑ j : Fin 24,
          ((orbitalGauge g u) i * (orbitalGauge g v) j) •
            wedgePairCoordinate i j) := by
    funext g
    calc
      fockCoordinates 23
          (exteriorGauge g
            (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v)) =
        fockCoordinates 23
          (ExteriorAlgebra.ι ℂ (orbitalGauge g u) *
            ExteriorAlgebra.ι ℂ (orbitalGauge g v)) := by
              simp only [exteriorGauge, map_mul,
                ExteriorAlgebra.map_apply_ι]
      _ = ∑ i : Fin 24, ∑ j : Fin 24,
            ((orbitalGauge g u) i * (orbitalGauge g v) j) •
              wedgePairCoordinate i j :=
          wedgePairCoordinate_expansion (orbitalGauge g u)
            (orbitalGauge g v)
  rw [he]
  exact hpoly

/-- In particular, two fixed genuine fermionic orbitals have a
continuous SU(2) image, including the antisymmetric wedge sign. -/
theorem exteriorGauge_modePair_coordinates_continuous
    (i j : Fin 24) :
    Continuous (fun g : GaugeGroup 2 =>
      fockCoordinates 23
        (exteriorGauge g
          (ExteriorAlgebra.ι ℂ (mode i) *
            ExteriorAlgebra.ι ℂ (mode j)))) :=
  exteriorGauge_wedgePair_coordinates_continuous (mode i) (mode j)

#print axioms wedgePairCoordinate
#print axioms wedgePairCoordinate_expansion
#print axioms exteriorGauge_wedgePair_coordinates_continuous
#print axioms exteriorGauge_modePair_coordinates_continuous

end
end FCP.BFSSSU2GaugeG4IB2
