import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD3AKineticGaugeContractionProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K9DSourcePotentialMultiplierProbe
import OAI.MathematicalPhysics.BFSS.CovariantFields

/-!
# BFSS SU(2) physical-domain D3B — original supercharge preserves gauge invariance

PROSPECTIVE / UNCOMPILED until the dedicated pinned Actions gate succeeds.
Every definition is the genuine pinned OAI source. The kinetic gauge
contraction is the newly qualified D3A result, and the potential
covariance is the original OAI BFSS source theorem.

Proves membership of original core charge images in the exact source
GaugeData.physicalSpace. Does NOT assert physical smooth-core density,
equality of a paper Hamiltonian, or new spectral results.
-/

namespace FCP.BFSSSU2PhysicalDomainD3B
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG4K9D
open FCP.BFSSSU2PhysicalDomainD3A
open Finset MeasureTheory

/-- Source original deformed charge decomposes *definitionally* into
the actual skew kinetic-symbol contraction and actual source potential.
No new operator or physical parameter is introduced. -/
theorem sourceDeformedCoreCharge_contracted
    {N : ℕ} (M : AlgebraData N)
    (α : SpinIndex) (f : SmoothCore N) (x : Boson N) :
    M.deformedCoreCharge 1 0 α f x =
      (∑ p : SpaceIndex × ColorIndex N,
        M.kineticSkewLinear α (EuclideanSpace.single p 1)
          (fderiv ℝ (f : Boson N → Fermion N) x
            (EuclideanSpace.single p 1))) +
      M.deformedPotentialMultiplier 1 0 x α (f x) := by
  change MixedEnergy.firstOrder (M.kineticSkewSymbol α) f x +
    MixedEnergy.field (M.deformedRealField 1 0 α)
      (M.deformedRealField_contDiff 1 0 α) f x = _
  rw [MixedEnergy.firstOrder_apply]
  simp only [MixedEnergy.delta_apply, MixedEnergy.field_apply,
    ← M.kineticSkewLinear_basis]
  rfl

/-- The actual source deformed supercharge is gauge-covariant on
every source invariant compactly supported smooth section. This
combines genuine D3A kinetic covariance and original potential
covariance, including the transformed fermion argument. -/
theorem sourceDeformedCoreCharge_pointwiseGaugeCovariant
    {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)
    (α : SpinIndex) (f : G.invariantCore)
    (g : GaugeGroup N) (x : Boson N) :
    M.deformedCoreCharge 1 0 α f.val (G.boson g x) =
      G.fermion g (M.deformedCoreCharge 1 0 α f.val x) := by
  rw [sourceDeformedCoreCharge_contracted M α f.val (G.boson g x),
      sourceDeformedCoreCharge_contracted M α f.val x, map_add]
  congr 1
  · exact sourceContractedKinetic_gaugeCovariant M G α f g x
  · rw [G.invariantCore_equivariant f g x]
    exact (G.deformedPotentialMultiplier_covariant g 1 0 x α (f.val x)).symm

/-- Transfer the pointwise covariance theorem to the literal
*original* BFSS source charge using the unconditionally qualified
massless source charge identity G4-K9D. -/
theorem sourceOriginalCoreCharge_pointwiseGaugeCovariant
    {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)
    (α : SpinIndex) (f : G.invariantCore)
    (g : GaugeGroup N) (x : Boson N) :
    M.charge α f.val (G.boson g x) =
      G.fermion g (M.charge α f.val x) := by
  simpa only [sourceUnconditionalCoreCharge_equal M α f.val] using
    sourceDeformedCoreCharge_pointwiseGaugeCovariant M G α f g x

/-- The ORIGINAL source charge of a source-invariant smooth-core
section is in the TRUE source physical Hilbert-space submodule,
defined as the intersection of pullback-minus-fiber kernels. -/
theorem sourceOriginalCoreCharge_mem_physicalSpace
    {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)
    (α : SpinIndex) (f : G.invariantCore) :
    coreToL2 (M.charge α f.val) ∈ G.physicalSpace := by
  change coreToL2 (M.charge α f.val) ∈
    (⨅ g : GaugeGroup N,
      LinearMap.ker (G.bosonPullback g - G.fiberAction g))
  rw [Submodule.mem_iInf]
  intro g
  change (G.bosonPullback g - G.fiberAction g)
    (coreToL2 (M.charge α f.val)) = 0
  apply sub_eq_zero.mpr
  apply Lp.ext_iff.mpr
  have hcomp := Lp.coeFn_compMeasurePreserving
    (coreToL2 (M.charge α f.val))
    (G.boson g).measurePreserving
  have hfiber := ContinuousLinearMap.coeFn_compLp
    (G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap
    (coreToL2 (M.charge α f.val))
  have hraw := (coreToL2_ae (M.charge α f.val)).comp_tendsto
    (G.boson g).measurePreserving.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hcomp, hfiber, hraw, coreToL2_ae (M.charge α f.val)]
    with x hc hf hr hv
  calc
    (G.bosonPullback g (coreToL2 (M.charge α f.val)) :
        Boson N → Fermion N) x =
      (coreToL2 (M.charge α f.val) : Boson N → Fermion N)
        (G.boson g x) := hc
    _ = M.charge α f.val (G.boson g x) := hr
    _ = G.fermion g (M.charge α f.val x) :=
      sourceOriginalCoreCharge_pointwiseGaugeCovariant M G α f g x
    _ = G.fermion g
          ((coreToL2 (M.charge α f.val) : Boson N → Fermion N) x) := by
            rw [← hv]
    _ = (G.fiberAction g (coreToL2 (M.charge α f.val)) :
          Boson N → Fermion N) x := hf.symm

/-- Stronger exact source conclusion: each original supercharge sends
every genuine invariant source SmoothCore section back into
G.invariantCore, not merely into an arbitrary full-space graph. -/
theorem sourceOriginalCoreCharge_mem_invariantCore
    {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)
    (α : SpinIndex) (f : G.invariantCore) :
    M.charge α f.val ∈ G.invariantCore := by
  change coreToL2 (M.charge α f.val) ∈ G.physicalSpace
  exact sourceOriginalCoreCharge_mem_physicalSpace M G α f

#print axioms sourceDeformedCoreCharge_contracted
#print axioms sourceDeformedCoreCharge_pointwiseGaugeCovariant
#print axioms sourceOriginalCoreCharge_pointwiseGaugeCovariant
#print axioms sourceOriginalCoreCharge_mem_physicalSpace
#print axioms sourceOriginalCoreCharge_mem_invariantCore

end
end FCP.BFSSSU2PhysicalDomainD3B
