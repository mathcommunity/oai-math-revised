import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AKOriginalFullL2ParityBosonGaugeProbe

/-!
# H5E8AL — true original SU2 FullL2 physical parity

AK established that actual L2 spatial parity commutes with the ORIGINAL
source GaugeData.bosonPullback. Here commute it with the ORIGINAL
GaugeData.fiberAction (the true Fock unitary applied pointwise), then
deduce preservation of the ORIGINAL source GaugeData.physicalSpace
and GaugeData.invariantCore — no proxy invariant subspace.

This remains a research candidate until source-pinned strict Lean CI.
Actual physical 16-charge *closed graph*, normalized Hamiltonian
operator domain and manuscript model equivalence remain separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AL
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AF
open FCP.BFSSSU2PhysicalDomainL6H5E8AI
open FCP.BFSSSU2PhysicalDomainL6H5E8AK
open MeasureTheory

/-- Actual original fermionic gauge action is pointwise in the bosonic
variable; spatial inversion therefore commutes with it on true L2. -/
theorem originalFullL2Parity_fiberAction {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) (g : GaugeGroup N)
    (v : FullL2 N) :
    originalFullL2Parity (G.fiberAction g v) =
      G.fiberAction g (originalFullL2Parity v) := by
  let L : Fermion N →L[ℂ] Fermion N :=
    (G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap
  have hleft := originalFullL2Parity_apply_ae (G.fiberAction g v)
  -- The generic compLp lemma produces an Eventually equality; give it
  -- explicit EventuallyEq syntax so comp_tendsto uses the correct lemma.
  have hfiber : (fun x : Boson N => (G.fiberAction g v) x) =ᵐ[volume]
      (fun x : Boson N => L (v x)) := by
    exact ContinuousLinearMap.coeFn_compLp L v
  have hfiberNeg := hfiber.comp_tendsto
    (originalBosonNeg_measurePreserving (N := N)).quasiMeasurePreserving.tendsto_ae
  have hright := originalFullL2Parity_apply_ae v
  have hfiberRight :=
    ContinuousLinearMap.coeFn_compLp L (originalFullL2Parity v)
  apply Lp.ext
  filter_upwards [hleft, hfiberNeg, hright, hfiberRight]
    with x hpx hfx hqx hfrx
  calc
    (originalFullL2Parity (G.fiberAction g v)) x =
      (G.fiberAction g v) (-x) := hpx
    _ = L (v (-x)) := hfx
    _ = L ((originalFullL2Parity v) x) :=
      congrArg L hqx.symm
    _ = (G.fiberAction g (originalFullL2Parity v)) x :=
      hfrx.symm

/-- Actual source physicalSpace is defined by all literal
G.bosonPullback g - G.fiberAction g kernels. Combining AK with the
fiber lemma shows FullL2 spatial parity preserves *that* submodule. -/
theorem originalFullL2Parity_mem_physicalSpace {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    {v : FullL2 N} (hv : v ∈ G.physicalSpace) :
    originalFullL2Parity v ∈ G.physicalSpace := by
  have hv' : v ∈
      (⨅ g : GaugeGroup N,
        LinearMap.ker (G.bosonPullback g - G.fiberAction g)) := hv
  change originalFullL2Parity v ∈
    (⨅ g : GaugeGroup N,
      LinearMap.ker (G.bosonPullback g - G.fiberAction g))
  apply (Submodule.mem_iInf _).mpr
  intro g
  have hv_g : G.bosonPullback g v = G.fiberAction g v := by
    have hg : v ∈
        LinearMap.ker (G.bosonPullback g - G.fiberAction g) :=
      (Submodule.mem_iInf _).mp hv' g
    change (G.bosonPullback g - G.fiberAction g) v = 0 at hg
    exact sub_eq_zero.mp (by
      simpa only [LinearMap.sub_apply] using hg)
  change G.bosonPullback g (originalFullL2Parity v) -
    G.fiberAction g (originalFullL2Parity v) = 0
  apply sub_eq_zero.mpr
  calc
    G.bosonPullback g (originalFullL2Parity v) =
        originalFullL2Parity (G.bosonPullback g v) :=
      (originalFullL2Parity_bosonPullback M G g v).symm
    _ = originalFullL2Parity (G.fiberAction g v) :=
      congrArg originalFullL2Parity hv_g
    _ = G.fiberAction g (originalFullL2Parity v) :=
      originalFullL2Parity_fiberAction M G g v

/-- Literal source smooth gauge-invariant core is also preserved:
the accepted source embedding P₂∘coreToL2 = coreToL2∘P makes
this a consequence of actual Hilbert-space physical invariance. -/
theorem originalSmoothParity_mem_invariantCore {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (f : G.invariantCore) :
    originalSmoothParity f.val ∈ G.invariantCore := by
  have hf : coreToL2 f.val ∈ G.physicalSpace := f.property
  change coreToL2 (originalSmoothParity f.val) ∈ G.physicalSpace
  rw [← originalFullL2Parity_coreToL2 f.val]
  exact originalFullL2Parity_mem_physicalSpace M G hf

#print axioms originalFullL2Parity_fiberAction
#print axioms originalFullL2Parity_mem_physicalSpace
#print axioms originalSmoothParity_mem_invariantCore

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AL
