import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2AClosedPhysicalGraphProbe
import OAI.Analysis.Laughlin.Spin.Haar

/-!
# BFSS physical-domain D2B1 — source SU(2) Haar equivariant averaging

PROSPECTIVE / UNCOMPILED until dedicated pinned CI succeeds.

The gauge group is the original BFSS `GaugeGroup 2`, definitionally
the SAME matrix SU(2) as upstream Laughlin.Rotation.SourceSU2. The
normalized Haar probability is the pre-existing SOURCE
OAI.Laughlin.Rotation.sourceHaar; it is NOT an invented measure,
projection or additional hypothesis.

D2B1 proves the group-average integrand is continuous, its average
is equivariant under the actual source BFSS gauge action, and it
fixes genuine gauge-invariant source smooth-core sections.

D2B1 does NOT yet prove the average is smooth and compactly supported,
bounded in L², or that physical smooth-core is L²-dense.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B1
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open OAI.Laughlin.Rotation
open MeasureTheory

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Source-typed fermion-valued Haar gauge average on the original
smooth-core function. The integral is over the SAME SU(2) gauge
group as GaugeData and uses upstream normalized Haar probability. -/
noncomputable def sourceHaarAverageRaw (f : SmoothCore 2)
    (x : Boson 2) : Fermion 2 :=
  ∫ g : GaugeGroup 2, G.fermion g (f (G.boson g⁻¹ x)) ∂sourceHaar

/-- Actual source joint-continuous boson/fermion actions imply
continuity of every SU(2) Haar average integrand. -/
theorem sourceHaarIntegrand_continuous (f : SmoothCore 2)
    (x : Boson 2) :
    Continuous (fun g : GaugeGroup 2 =>
      G.fermion g (f (G.boson g⁻¹ x))) := by
  have hc : Continuous (fun g : GaugeGroup 2 => G.boson g⁻¹ x) :=
    G.boson_continuous.comp (continuous_inv.prodMk continuous_const)
  exact G.fermion_continuous.comp (continuous_id.prodMk (f.continuous.comp hc))

/-- Normed Bochner integrability of the ACTUAL source gauge-average
integrand, using the existing compact SU(2) Haar probability. -/
theorem sourceHaarIntegrand_integrable (f : SmoothCore 2)
    (x : Boson 2) :
    Integrable (fun g : GaugeGroup 2 =>
      G.fermion g (f (G.boson g⁻¹ x))) sourceHaar := by
  exact (sourceHaarIntegrand_continuous M G f x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The genuine BFSS fermion-valued Haar average is equivariant under
the source-defined SU(2) gauge action, for arbitrary smooth test
sections. Invariant-core membership still requires smoothness and
compact support of the averaged section, not claimed here. -/
theorem sourceHaarAverageRaw_equivariant (f : SmoothCore 2)
    (h : GaugeGroup 2) (x : Boson 2) :
    sourceHaarAverageRaw M G f (G.boson h x) =
      G.fermion h (sourceHaarAverageRaw M G f x) := by
  have hshift := integral_mul_left_eq_self (μ := sourceHaar)
    (fun g : GaugeGroup 2 =>
      G.fermion g (f (G.boson g⁻¹ (G.boson h x)))) h
  have hpoint (g : GaugeGroup 2) :
      G.fermion (h * g)
          (f (G.boson (h * g)⁻¹ (G.boson h x))) =
        G.fermion h (G.fermion g (f (G.boson g⁻¹ x))) := by
    -- The genuine group homomorphisms are multiplicative, and
    -- linear-isometry equivalence multiplication acts by composition.
    -- No bespoke mul_apply lemma is needed.
    simp [mul_inv_rev, map_mul, map_inv]
  calc
    sourceHaarAverageRaw M G f (G.boson h x) =
      ∫ g : GaugeGroup 2,
        G.fermion (h * g)
          (f (G.boson (h * g)⁻¹ (G.boson h x))) ∂sourceHaar := by
            unfold sourceHaarAverageRaw
            exact hshift.symm
    _ = ∫ g : GaugeGroup 2,
        G.fermion h (G.fermion g
          (f (G.boson g⁻¹ x))) ∂sourceHaar := by
            apply integral_congr_ae
            filter_upwards [] with g
            exact hpoint g
    _ = G.fermion h (sourceHaarAverageRaw M G f x) := by
          change (∫ g : GaugeGroup 2,
              (G.fermion h).toContinuousLinearEquiv.toContinuousLinearMap
                (G.fermion g (f (G.boson g⁻¹ x))) ∂sourceHaar) =
            (G.fermion h).toContinuousLinearEquiv.toContinuousLinearMap
              (∫ g : GaugeGroup 2,
                G.fermion g (f (G.boson g⁻¹ x)) ∂sourceHaar)
          exact (G.fermion h).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
            (sourceHaarIntegrand_integrable M G f x)

/-- The normalized group average fixes EVERY actual BFSS
gauge-invariant source smooth-core section. -/
theorem sourceHaarAverageRaw_fixed (f : G.invariantCore)
    (x : Boson 2) :
    sourceHaarAverageRaw M G f.val x = f.val x := by
  have hpoint (g : GaugeGroup 2) :
      G.fermion g (f.val (G.boson g⁻¹ x)) = f.val x := by
    rw [G.invariantCore_equivariant f g⁻¹ x]
    calc
      G.fermion g (G.fermion g⁻¹ (f.val x)) =
        G.fermion (g * g⁻¹) (f.val x) := by
          rw [map_mul]
          rfl
      _ = f.val x := by simp
  calc
    sourceHaarAverageRaw M G f.val x =
      ∫ g : GaugeGroup 2, f.val x ∂sourceHaar := by
        unfold sourceHaarAverageRaw
        apply integral_congr_ae
        filter_upwards [] with g
        exact hpoint g
    _ = f.val x := by simp

#print axioms sourceHaarIntegrand_continuous
#print axioms sourceHaarIntegrand_integrable
#print axioms sourceHaarAverageRaw_equivariant
#print axioms sourceHaarAverageRaw_fixed

end
end FCP.BFSSSU2PhysicalDomainD2B1
