import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K7EnergySumOfSquaresCorrectionProbe

/-!
# BFSS SU(2) G4-K8A — the concrete Gauss state has a nonzero bosonic derivative

G4-K7 (Gate #138) proves that strict trial energy is equivalent
to a nonzero source-defined deformed supercharge component.
Here we begin discharging that genuine analytical obligation,
without claiming it is already solved.

For the EXACT SU(2)-invariant radialBumpSmoothCore from Gate #132,
exhibit one explicitly named point outside its closed unit-ball
support, show that its value there is zero while its value at the
origin is nonzero, and deduce by the pinned Mathlib mean-value
theorem that its REAL Frechet derivative is nonzero somewhere.

This concerns the actual nonzero, normalizable, SU(2)-physical
48-Majorana, 24-orbital BFSS N=2 state. It does NOT yet prove
a coordinate-derivative L² norm or a deformed supercharge
component is nonzero, nor strict energy, a spectral gap,
energy eigenstate, zero mode or supersymmetric ground state.
-/

namespace FCP.BFSSSU2GaugeG4K8A
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4K2A
open FCP.BFSSSU2GaugeG4K2B
open FCP.BFSSSU2GaugeG4K3

/-- Genuine BFSS N=2 bosonic configuration with one spatial/color
coordinate set to 2. This lies outside the bump's support. -/
noncomputable def radialFarPoint : Boson 2 :=
  EuclideanSpace.single ((0 : SpaceIndex), (⟨0, by decide⟩ : ColorIndex 2)) (2 : ℝ)

/-- Its norm is at least one in the literal EuclideanSpace metric. -/
theorem radialFarPoint_norm_ge_one : 1 ≤ ‖radialFarPoint‖ := by
  unfold radialFarPoint
  rw [EuclideanSpace.norm_single]
  norm_num

/-- The accepted actual smooth Gauss state is NONZERO at
the origin by the source-certified nonzero Fock vacuum. -/
theorem radialBumpSmoothCore_center_nonzero :
    radialBumpSmoothCore (0 : Boson 2) ≠ 0 := by
  change radialVacuumProfile radialBumpCoefficient (0 : Boson 2) ≠ 0
  exact radialVacuumProfile_nonzero_at_origin _
    radialBumpCoefficient_zero

/-- The very same accepted state is EXACTLY ZERO at the
concrete far point by its proved compact radial support. -/
theorem radialBumpSmoothCore_far_zero :
    radialBumpSmoothCore radialFarPoint = 0 := by
  change radialVacuumProfile radialBumpCoefficient radialFarPoint = 0
  exact radialBumpProfile_zero_of_large _
    radialFarPoint_norm_ge_one

/-- The accepted physical smooth state cannot be constant on
the real BFSS bosonic configuration space. -/
theorem radialBumpSmoothCore_not_constant :
    ¬ ∀ x : Boson 2, radialBumpSmoothCore x =
      radialBumpSmoothCore (0 : Boson 2) := by
  intro h
  exact radialBumpSmoothCore_center_nonzero
    ((h radialFarPoint).symm.trans radialBumpSmoothCore_far_zero)

/-- New mathematical obligation: the exact nonzero SU(2)
physical test state has a GENUINELY NONZERO real Frechet
derivative at some configuration. Follows from the genuine
two-point contrast and the pinned `is_const_of_fderiv_eq_zero`.

This does NOT assert that any particular source supercharge
or coordinate derivative image in FullL2 is nonzero. -/
theorem radialBumpSmoothCore_exists_nonzero_fderiv :
    ∃ x : Boson 2,
      fderiv ℝ (radialBumpSmoothCore : Boson 2 → Fermion 2) x ≠ 0 := by
  classical
  by_contra hn
  have hzero (x : Boson 2) :
      fderiv ℝ (radialBumpSmoothCore : Boson 2 → Fermion 2) x = 0 := by
    by_contra hx
    exact hn ⟨x, hx⟩
  have hdiff : Differentiable ℝ
      (radialBumpSmoothCore : Boson 2 → Fermion 2) :=
    radialBumpSmoothCore.contDiff.differentiable (by simp)
  have hconst :
      radialBumpSmoothCore (0 : Boson 2) =
        radialBumpSmoothCore radialFarPoint :=
    is_const_of_fderiv_eq_zero hdiff hzero
      (0 : Boson 2) radialFarPoint
  exact radialBumpSmoothCore_center_nonzero
    (hconst.trans radialBumpSmoothCore_far_zero)

#print axioms radialFarPoint
#print axioms radialFarPoint_norm_ge_one
#print axioms radialBumpSmoothCore_center_nonzero
#print axioms radialBumpSmoothCore_far_zero
#print axioms radialBumpSmoothCore_not_constant
#print axioms radialBumpSmoothCore_exists_nonzero_fderiv

end
end FCP.BFSSSU2GaugeG4K8A
