import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B9BFullL2HaarCLMProbe

/-!
# BFSS SU2 D2B9C — genuine full-L2 SU2 Haar projection onto physical space

PROSPECTIVE / UNCOMPILED until exact pinned CI gate passes.

D2B9B packaged the true-source FullL2 SU2 Haar integral as a
norm-contractive complex CLM. Here the group-action composition law
is proved for the original source-defined fermionic and bosonic
representations, with explicit a.e. equality on the source Lp space.

That identity and left-invariance of the exact source Haar measure
then show that Haar averaging lands in the exact source-defined
physicalSpace; original physical vectors are already fixed by
the accepted D2B9A/D2B9B results.

No assumed gauge representation, independent mock projection,
or physical-spectrum claim is introduced. Smooth-core compatibility
and coreNormClosure = physicalSpace remain open.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B9C
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open OAI.Laughlin.Rotation
open FCP.BFSSSU2PhysicalDomainD2B6
open FCP.BFSSSU2PhysicalDomainD2B7
open FCP.BFSSSU2PhysicalDomainD2B8A
open FCP.BFSSSU2PhysicalDomainD2B9A
open FCP.BFSSSU2PhysicalDomainD2B9B
open MeasureTheory

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The exact original full-Hilbert gauge action has the same
a.e. representative as the true source gauge integrand.
This holds for ALL original full-L2 vectors, not just the smooth core. -/
theorem sourceFullGaugePairCLM_ae (g : GaugeGroup 2) (v : FullL2 2) :
    (sourceFullGaugePairCLM M G g v : Boson 2 → Fermion 2) =ᵐ[volume]
      (fun x => G.fermion g (v (G.boson g⁻¹ x))) := by
  have hb := Lp.coeFn_compMeasurePreserving v
    (G.boson g⁻¹).measurePreserving
  have hf := ContinuousLinearMap.coeFn_compLp
    (G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap
    (G.bosonPullback g⁻¹ v)
  filter_upwards [hf, hb] with x hfx hbx
  calc
    (sourceFullGaugePairCLM M G g v) x =
      (G.fiberAction g (G.bosonPullback g⁻¹ v)) x := by
        rw [sourceFullGaugePairCLM_apply]
    _ = G.fermion g ((G.bosonPullback g⁻¹ v) x) := hfx
    _ = G.fermion g (v (G.boson g⁻¹ x)) :=
      congrArg (G.fermion g) hbx

/-- The actual BFSS full-L2 gauge operators obey the SU2
representation multiplication law; only original source
bosonic pullbacks and fermionic fiber actions are used. -/
theorem sourceFullGaugePairCLM_mul
    (g h : GaugeGroup 2) (v : FullL2 2) :
    sourceFullGaugePairCLM M G g (sourceFullGaugePairCLM M G h v) =
      sourceFullGaugePairCLM M G (g * h) v := by
  apply Lp.ext
  have ho := sourceFullGaugePairCLM_ae M G g
    (sourceFullGaugePairCLM M G h v)
  have hi := (sourceFullGaugePairCLM_ae M G h v).comp_tendsto
    (G.boson g⁻¹).measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hp := sourceFullGaugePairCLM_ae M G (g * h) v
  filter_upwards [ho, hi, hp] with x hox hix hpx
  calc
    (sourceFullGaugePairCLM M G g
        (sourceFullGaugePairCLM M G h v)) x =
      G.fermion g ((sourceFullGaugePairCLM M G h v)
        (G.boson g⁻¹ x)) := hox
    _ = G.fermion g (G.fermion h
        (v (G.boson h⁻¹ (G.boson g⁻¹ x)))) :=
          congrArg (G.fermion g) hix
    _ = G.fermion (g * h)
        (v (G.boson (g * h)⁻¹ x)) := by
          simp [mul_inv_rev, map_mul, map_inv]
    _ = (sourceFullGaugePairCLM M G (g * h) v) x := hpx.symm

/-- The source Haar CLM maps every original FullL2 state into
the exact original GaugeData.physicalSpace. This is the
missing full-Hilbert projection-range half. -/
theorem sourceFullHaarAverageCLM_mem_physical (v : FullL2 2) :
    sourceFullHaarAverageCLM M G v ∈ G.physicalSpace := by
  apply (sourceFullGaugePairCLM_fixed_iff_physical M G
    (sourceFullHaarAverageCLM M G v)).mp
  intro h
  rw [sourceFullHaarAverageCLM_apply]
  change sourceFullGaugePairCLM M G h
    (∫ g : GaugeGroup 2, sourceFullGaugePairCLM M G g v ∂sourceHaar) =
      (∫ g : GaugeGroup 2, sourceFullGaugePairCLM M G g v ∂sourceHaar)
  calc
    _ = ∫ g : GaugeGroup 2,
        sourceFullGaugePairCLM M G h (sourceFullGaugePairCLM M G g v)
          ∂sourceHaar :=
        ((sourceFullGaugePairCLM M G h).integral_comp_comm
          (sourceFullHaarIntegrand_integrable M G v)).symm
    _ = ∫ g : GaugeGroup 2, sourceFullGaugePairCLM M G (h * g) v
          ∂sourceHaar := by
        apply integral_congr_ae
        filter_upwards [] with g
        exact sourceFullGaugePairCLM_mul M G h g v
    _ = _ := integral_mul_left_eq_self
      (fun g : GaugeGroup 2 => sourceFullGaugePairCLM M G g v) h

/-- The true-source Haar operator is a genuine idempotent
continuous complex-linear operator on the original FullL2 space. -/
theorem sourceFullHaarAverageCLM_idempotent (v : FullL2 2) :
    sourceFullHaarAverageCLM M G
      (sourceFullHaarAverageCLM M G v) =
      sourceFullHaarAverageCLM M G v := by
  exact sourceFullHaarAverageCLM_fixed_physical M G _
    (sourceFullHaarAverageCLM_mem_physical M G v)

/-- Its range is EXACTLY the source-defined physical Hilbert
submodule, not merely a contained abstract fixed-point space. -/
theorem sourceFullHaarAverageCLM_range_eq_physical :
    LinearMap.range (sourceFullHaarAverageCLM M G).toLinearMap =
      G.physicalSpace := by
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    exact sourceFullHaarAverageCLM_mem_physical M G v
  · intro v hv
    exact ⟨v, sourceFullHaarAverageCLM_fixed_physical M G v hv⟩

#print axioms sourceFullGaugePairCLM_ae
#print axioms sourceFullGaugePairCLM_mul
#print axioms sourceFullHaarAverageCLM_mem_physical
#print axioms sourceFullHaarAverageCLM_idempotent
#print axioms sourceFullHaarAverageCLM_range_eq_physical

end
end FCP.BFSSSU2PhysicalDomainD2B9C
