import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG3CComplexOneParticleUnitaryProbe
import OAI.Analysis.Laughlin.Exterior.SpinAction

/-!
# BFSS SU(2) G4-A — genuine 24-orbital exterior-algebra gauge action

Source-bound by the accepted G3-C complexOneParticleMatrix g : 24×24 ℂ.
Unlike the separate upstream SourceSU2 spin rotation, this is the
precise BFSS color-adjoint matrix for eight spin pairs and three colors.

G4-A proves a real action on the pinned Laughlin.Fock.Space 23
exterior algebra and the actual creators/annihilators. It does NOT
yet claim isometry on the 2^24-dimensional Fock Hilbert space,
theta covariance or the complete BFSS GaugeData.
-/

namespace FCP.BFSSSU2GaugeG4A
noncomputable section

open Matrix Finset
open OAI.BFSSQuantum
open OAI.Laughlin.Fock
open FCP.BFSSSU2GaugeG3C

/-- Exact BFSS SU(2) color matrix acting on the 24 one-particle
orbital amplitudes by ordinary matrix-vector multiplication. -/
noncomputable def orbitalGauge (g : GaugeGroup 2) :
    Orbital 23 →ₗ[ℂ] Orbital 23 where
  toFun v := complexOneParticleMatrix g *ᵥ v
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' c v := Matrix.mulVec_smul _ c v

/-- The identity SU(2) matrix acts as the identity orbital map. -/
theorem orbitalGauge_one : orbitalGauge (1 : GaugeGroup 2) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext i
  change (complexOneParticleMatrix (1 : GaugeGroup 2) *ᵥ v) i = v i
  rw [complexOneParticleMatrix_one]
  simp

/-- The exact SU(2) group composition, with colors not transposed. -/
theorem orbitalGauge_mul (g h : GaugeGroup 2) :
    (orbitalGauge g).comp (orbitalGauge h) = orbitalGauge (g*h) := by
  apply LinearMap.ext
  intro v
  funext i
  change (complexOneParticleMatrix g *ᵥ
    (complexOneParticleMatrix h *ᵥ v)) i =
      (complexOneParticleMatrix (g*h) *ᵥ v) i
  rw [Matrix.mulVec_mulVec, ← complexOneParticleMatrix_mul]

/-- The genuine exterior-algebra map induced by the 24-mode BFSS
color rotation. This is not yet a Hilbert-isometry structure. -/
noncomputable def exteriorGauge (g : GaugeGroup 2) :
    Space 23 →ₐ[ℂ] Space 23 :=
  ExteriorAlgebra.map (orbitalGauge g)

theorem exteriorGauge_one (x : Space 23) :
    exteriorGauge (1 : GaugeGroup 2) x = x := by
  unfold exteriorGauge
  rw [orbitalGauge_one, ExteriorAlgebra.map_id]
  rfl

theorem exteriorGauge_mul (g h : GaugeGroup 2) (x : Space 23) :
    exteriorGauge g (exteriorGauge h x) = exteriorGauge (g*h) x := by
  change ((ExteriorAlgebra.map (orbitalGauge g)).comp
    (ExteriorAlgebra.map (orbitalGauge h))) x = _
  rw [ExteriorAlgebra.map_comp_map, orbitalGauge_mul]
  rfl

theorem exteriorGauge_inv (g : GaugeGroup 2) (x : Space 23) :
    exteriorGauge g⁻¹ (exteriorGauge g x) = x := by
  rw [exteriorGauge_mul, inv_mul_cancel, exteriorGauge_one]

/-- The algebraic exterior vacuum (unit) is fixed by every gauge map. -/
theorem exteriorGauge_vacuum (g : GaugeGroup 2) :
    exteriorGauge g (1 : Space 23) = 1 :=
  map_one (exteriorGauge g)

/-- The genuine BFSS 24-mode orbital transformation of coordinate
evaluation, used by the contraction/annihilation covariance. -/
theorem projection_orbitalGauge (g : GaugeGroup 2) (i : Fin 24) :
    (LinearMap.proj i).comp (orbitalGauge g) =
      ∑ j : Fin 24, complexOneParticleMatrix g i j • LinearMap.proj j := by
  ext v
  simp [orbitalGauge, Matrix.mulVec, dotProduct, LinearMap.proj]

/-- Actual exterior annihilators transform by the input-projecting
row coefficients U(g) i j. Not a formal placeholder CAR. -/
theorem annihilate_exteriorGauge
    (g : GaugeGroup 2) (i : Fin 24) (x : Space 23) :
    annihilate i (exteriorGauge g x) =
      ∑ j : Fin 24, complexOneParticleMatrix g i j •
        exteriorGauge g (annihilate j x) := by
  unfold annihilate exteriorGauge
  rw [contraction_map, projection_orbitalGauge]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

/-- Actual exterior creators transform by the output-color column
coefficients U(g) j i, preserving the accepted spin/color labeling. -/
theorem create_exteriorGauge
    (g : GaugeGroup 2) (i : Fin 24) (x : Space 23) :
    exteriorGauge g (create i x) =
      ∑ j : Fin 24, complexOneParticleMatrix g j i •
        create j (exteriorGauge g x) := by
  change ExteriorAlgebra.map (orbitalGauge g)
    (ExteriorAlgebra.ι ℂ (mode i) * x) = _
  rw [map_mul, ExteriorAlgebra.map_apply_ι,
    orbital_sum_modes 23 (orbitalGauge g (mode i))]
  simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro j hj
  have he : orbitalGauge g (mode i) j = complexOneParticleMatrix g j i := by
    simp [orbitalGauge, mode, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [he]
  rfl

#print axioms orbitalGauge_one
#print axioms orbitalGauge_mul
#print axioms exteriorGauge_one
#print axioms exteriorGauge_mul
#print axioms exteriorGauge_inv
#print axioms exteriorGauge_vacuum
#print axioms projection_orbitalGauge
#print axioms annihilate_exteriorGauge
#print axioms create_exteriorGauge

end
end FCP.BFSSSU2GaugeG4A
