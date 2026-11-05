import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K8ANonzeroDerivativeProbe

/-!
# BFSS SU(2) G4-K8B — genuine nonzero coordinate derivative in FullL2

Gate #140 proved that the exact compactly supported nonzero SU(2)
physical radial smooth-core state has a NONZERO REAL FRECHET
DERIVATIVE at some actual bosonic configuration. Here transport
this fact through the source-defined finite Euclidean coordinate
basis and the literal source coordinateDerivative operators,
then from a nonzero continuous section to a NONZERO FullL2
equivalence class. Finish with the actual kinetic-density
integral identity from Gate #135, proving strict positivity
of the integrated kinetic density for this same Gauss state.

This is not yet nonvanishing of any DEFORMED SUPERCHARGE.
Kinetic and fermionic/potential terms could cancel within
the deformed supercharge. No strict total deformed energy,
energy eigenstate, supersymmetric ground state, BFSS gap,
or physics prediction is asserted.
-/

namespace FCP.BFSSSU2GaugeG4K8B
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open MeasureTheory
open FCP.BFSSSU2GaugeG4K2B
open FCP.BFSSSU2GaugeG4K3
open FCP.BFSSSU2GaugeG4K5
open FCP.BFSSSU2GaugeG4K8A

/-- At some actual configuration, one PINNED bosonic coordinate
derivative of the accepted invariant smooth test state is nonzero.
The bridge from the full Fréchet derivative uses the COMPLETE
finite coordinate basis of the exact upstream Boson 2. -/
theorem exists_coordinateDerivative_pointwise_ne_zero :
    ∃ p : SpaceIndex × ColorIndex 2, ∃ x : Boson 2,
      coordinateDerivative p.1 p.2 radialBumpSmoothCore x ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := radialBumpSmoothCore_exists_nonzero_fderiv
  by_contra hn
  have hzero (p : SpaceIndex × ColorIndex 2) :
      (fderiv ℝ (radialBumpSmoothCore : Boson 2 → Fermion 2) x)
        (EuclideanSpace.single p 1) = 0 := by
    by_contra hp
    apply hn
    refine ⟨p, x, ?_⟩
    simpa only [coordinateDerivative_apply] using hp
  have hlin :
      (fderiv ℝ (radialBumpSmoothCore : Boson 2 → Fermion 2) x).toLinearMap =
        (0 : Boson 2 →ₗ[ℝ] Fermion 2) := by
    apply (EuclideanSpace.basisFun (SpaceIndex × ColorIndex 2) ℝ).toBasis.ext
    intro p
    simpa only [OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply, LinearMap.zero_apply,
      ContinuousLinearMap.coe_coe] using hzero p
  apply hx
  apply ContinuousLinearMap.ext
  intro v
  exact DFunLike.congr_fun hlin v

/-- A nonzero coordinate derivative AT A POINT yields a NONZERO
L² equivalence class, because the true coordinateDerivative is
continuous and Euclidean volume has positive measure on opens.
No single-point-measure fallacy is permitted. -/
theorem coordinateDerivative_coreToL2_ne_zero_of_point
    (p : SpaceIndex × ColorIndex 2) (x : Boson 2)
    (hx : coordinateDerivative p.1 p.2 radialBumpSmoothCore x ≠ 0) :
    coreToL2 (coordinateDerivative p.1 p.2 radialBumpSmoothCore) ≠ 0 := by
  intro hz
  have hae :
      (coordinateDerivative p.1 p.2 radialBumpSmoothCore : Boson 2 → Fermion 2)
        =ᵐ[volume] (fun _ : Boson 2 => (0 : Fermion 2)) :=
    (coreToL2_ae (coordinateDerivative p.1 p.2 radialBumpSmoothCore)).symm.trans
      ((Lp.ext_iff.mp hz).trans
        (Lp.coeFn_zero (E := Fermion 2) (p := 2)
          (μ := (volume : Measure (Boson 2)))))
  have hevery :
      (coordinateDerivative p.1 p.2 radialBumpSmoothCore : Boson 2 → Fermion 2) =
        (fun _ : Boson 2 => (0 : Fermion 2)) :=
    (((coordinateDerivative p.1 p.2 radialBumpSmoothCore).continuous.ae_eq_iff_eq
      (volume : Measure (Boson 2)) continuous_const).mp hae)
  exact hx (congrFun hevery x)

/-- Real existence witness on the exact source FullL2 2:
at least one genuine coordinate derivative has nonzero L² norm. -/
theorem exists_coordinateDerivative_coreToL2_ne_zero :
    ∃ p : SpaceIndex × ColorIndex 2,
      coreToL2 (coordinateDerivative p.1 p.2 radialBumpSmoothCore) ≠ 0 := by
  obtain ⟨p, x, hx⟩ := exists_coordinateDerivative_pointwise_ne_zero
  exact ⟨p, coordinateDerivative_coreToL2_ne_zero_of_point p x hx⟩

/-- STRICT kinetic positivity for the actual nonzero,
smooth, Gauss-invariant physical BFSS SU(2) state.
Unlike energy nonnegativity, this uses a NEW nonzero
coordinate derivative in the true Hilbert L² space. -/
theorem physicalKineticDensity_integral_pos :
    0 < (∫ x : Boson 2, physicalKineticDensity x) := by
  rw [physicalKineticDensity_integral_exact]
  obtain ⟨p, hp⟩ := exists_coordinateDerivative_coreToL2_ne_zero
  apply Finset.sum_pos'
  · intro q hq
    exact sq_nonneg _
  · refine ⟨p, Finset.mem_univ _, ?_⟩
    exact pow_pos (norm_pos_iff.mpr hp) 2

/-- The literal source integrated kinetic density is
also nonzero. This is NOT positivity of full deformed
charge energy or a global spectral lower bound. -/
theorem physicalKineticDensity_integral_ne_zero :
    (∫ x : Boson 2, physicalKineticDensity x) ≠ 0 :=
  ne_of_gt physicalKineticDensity_integral_pos

#print axioms exists_coordinateDerivative_pointwise_ne_zero
#print axioms coordinateDerivative_coreToL2_ne_zero_of_point
#print axioms exists_coordinateDerivative_coreToL2_ne_zero
#print axioms physicalKineticDensity_integral_pos
#print axioms physicalKineticDensity_integral_ne_zero

end
end FCP.BFSSSU2GaugeG4K8B
