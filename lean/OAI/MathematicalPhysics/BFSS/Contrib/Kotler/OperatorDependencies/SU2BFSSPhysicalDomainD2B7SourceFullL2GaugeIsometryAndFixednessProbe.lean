import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B6SourceFullL2GaugeActionProbe

/-!
# BFSS SU2 D2B7 — original FullL2 gauge isometry, physical fixedness and core compatibility

PROSPECTIVE / UNCOMPILED until exact pinned CI validates all six axioms reports.

Work only with ORIGINAL GaugeData.bosonPullback, GaugeData.fiberAction,
FullL2 2, SmoothCore 2, the source physicalSpace, and the qualified
sourceFullGaugePairCLM built at D2B6. No new SU2 action or physics axiom.

This step does NOT prove Haar Bochner integrability on FullL2,
norm-contractive Haar projection, or coreNormClosure = physicalSpace.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B7
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B6
open FCP.BFSSSU2PhysicalDomainD2B5
open MeasureTheory

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The original fermion action on full L² inverts under SU2 inversion.
This uses the ORIGINAL fiberAction and the source fermion group homomorphism. -/
theorem sourceFermionFiberAction_left_inv
    (g : GaugeGroup 2) (v : FullL2 2) :
    G.fiberAction g (G.fiberAction g⁻¹ v) = v := by
  apply Lp.ext
  have hout := ContinuousLinearMap.coeFn_compLp
    (G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap
    (G.fiberAction g⁻¹ v)
  have hin := ContinuousLinearMap.coeFn_compLp
    (G.fermion g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap v
  filter_upwards [hout, hin] with x hx hy
  calc
    (G.fiberAction g (G.fiberAction g⁻¹ v)) x =
        G.fermion g ((G.fiberAction g⁻¹ v) x) := hx
    _ = G.fermion g (G.fermion g⁻¹ (v x)) :=
      congrArg (G.fermion g) hy
    _ = G.fermion (g * g⁻¹) (v x) := by rw [map_mul]; rfl
    _ = v x := by simp

/-- The genuine full-L² fiber gauge action is an ISOMETRY, not
merely the nonexpansive operator proved in D2B6. -/
theorem sourceFermionFiberAction_norm_eq
    (g : GaugeGroup 2) (v : FullL2 2) :
    ‖G.fiberAction g v‖ = ‖v‖ := by
  apply le_antisymm (sourceFermionFiberAction_norm_le M G g v)
  have h := sourceFermionFiberAction_left_inv M G g⁻¹ v
  simp only [inv_inv] at h
  calc
    ‖v‖ = ‖G.fiberAction g⁻¹ (G.fiberAction g v)‖ := congrArg norm h.symm
    _ ≤ ‖G.fiberAction g v‖ :=
      sourceFermionFiberAction_norm_le M G g⁻¹ _

/-- The exact source combined boson/fermion SU2 action preserves
the norm of every vector in the ORIGINAL BFSS full Hilbert space. -/
theorem sourceFullGaugePair_norm_eq
    (g : GaugeGroup 2) (v : FullL2 2) :
    ‖G.fiberAction g (G.bosonPullback g⁻¹ v)‖ = ‖v‖ := by
  rw [sourceFermionFiberAction_norm_eq M G g,
    sourceBosonPullback_norm M G g⁻¹ v]

/-- The new D2B6 continuous-linear-map packaging acts ISOMETRICALLY
on actual FullL2 vectors, rather than only having operator norm ≤ 1. -/
theorem sourceFullGaugePairCLM_norm_map
    (g : GaugeGroup 2) (v : FullL2 2) :
    ‖sourceFullGaugePairCLM M G g v‖ = ‖v‖ := by
  rw [sourceFullGaugePairCLM_apply]
  exact sourceFullGaugePair_norm_eq M G g v

/-- Every element of the EXACT original GaugeData.physicalSpace
is fixed by each exact full-L² SU2 gauge transformation.
No hypothetical or surrogate physical subspace is used. -/
theorem sourceFullGaugePairCLM_fixed_physical
    (g : GaugeGroup 2) (v : FullL2 2) (hv : v ∈ G.physicalSpace) :
    sourceFullGaugePairCLM M G g v = v := by
  have hv' : G.bosonPullback g⁻¹ v = G.fiberAction g⁻¹ v := by
    have hmem : v ∈
      (⨅ h : GaugeGroup 2,
        LinearMap.ker (G.bosonPullback h - G.fiberAction h)) := hv
    exact sub_eq_zero.mp ((Submodule.mem_iInf _).mp hmem g⁻¹)
  rw [sourceFullGaugePairCLM_apply, hv']
  exact sourceFermionFiberAction_left_inv M G g v

/-- The exact full-Hilbert-space gauge operator agrees almost
everywhere on coreToL2 images with the ORIGINAL source smooth
gauge integrand used by the already-proved Haar average. -/
theorem sourceFullGaugePairCLM_core_ae
    (f : SmoothCore 2) (g : GaugeGroup 2) :
    (sourceFullGaugePairCLM M G g (coreToL2 f) :
      Boson 2 → Fermion 2) =ᵐ[volume]
      (fun x => G.fermion g (f (G.boson g⁻¹ x))) := by
  have hb := Lp.coeFn_compMeasurePreserving (coreToL2 f)
    (G.boson g⁻¹).measurePreserving
  have hf := ContinuousLinearMap.coeFn_compLp
    (G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap
    (G.bosonPullback g⁻¹ (coreToL2 f))
  have ha := (coreToL2_ae f).comp_tendsto
    (G.boson g⁻¹).measurePreserving.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hf, hb, ha] with x hfx hbx hax
  calc
    (sourceFullGaugePairCLM M G g (coreToL2 f)) x =
        (G.fiberAction g (G.bosonPullback g⁻¹ (coreToL2 f))) x := by
          rw [sourceFullGaugePairCLM_apply]
    _ = G.fermion g ((G.bosonPullback g⁻¹ (coreToL2 f)) x) := hfx
    _ = G.fermion g ((coreToL2 f) (G.boson g⁻¹ x)) :=
      congrArg (G.fermion g) hbx
    _ = G.fermion g (f (G.boson g⁻¹ x)) :=
      congrArg (G.fermion g) hax

#print axioms sourceFermionFiberAction_left_inv
#print axioms sourceFermionFiberAction_norm_eq
#print axioms sourceFullGaugePair_norm_eq
#print axioms sourceFullGaugePairCLM_norm_map
#print axioms sourceFullGaugePairCLM_fixed_physical
#print axioms sourceFullGaugePairCLM_core_ae

end
end FCP.BFSSSU2PhysicalDomainD2B7
