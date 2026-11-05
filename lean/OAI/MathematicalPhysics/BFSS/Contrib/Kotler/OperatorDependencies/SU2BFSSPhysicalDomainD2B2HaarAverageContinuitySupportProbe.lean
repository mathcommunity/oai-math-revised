import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B1SourceHaarEquivariantAverageProbe
import OAI.Analysis.Laughlin.Spin.Haar

/-!
# BFSS physical-domain D2B2: continuous compactly supported Haar average

PROSPECTIVE / UNCOMPILED until pinned dedicated CI passes.
The construction uses exact source GaugeData, SU(2) Haar probability,
and the actual earlier D2B1 averaged Fermion 2-valued function.

D2B2 does not claim C∞ smoothness, L² contraction, L² density or
self-adjoint Hamiltonian correspondence.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B2
noncomputable section
open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open OAI.Laughlin.Rotation
open FCP.BFSSSU2PhysicalDomainD2B1
open MeasureTheory Set

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Genuine BFSS Haar average integrand is continuous in the
combined bosonic position and source SU2 group variable. -/
theorem sourceHaarIntegrand_jointContinuous (f : SmoothCore 2) :
    Continuous (fun p : Boson 2 × GaugeGroup 2 =>
      G.fermion p.2 (f (G.boson p.2⁻¹ p.1))) := by
  have hboson : Continuous (fun p : Boson 2 × GaugeGroup 2 =>
      G.boson p.2⁻¹ p.1) :=
    G.boson_continuous.comp ((continuous_snd.inv).prodMk continuous_fst)
  exact G.fermion_continuous.comp
    (continuous_snd.prodMk (f.continuous.comp hboson))

/-- The genuine fermion-valued SU2 Haar average is continuous in
the actual bosonic coordinate, using compact parametric integration
of the joint continuous source action. -/
theorem sourceHaarAverageRaw_continuous (f : SmoothCore 2) :
    Continuous (sourceHaarAverageRaw M G f) := by
  -- Work coordinatewise in the original Fermion 2 = EuclideanSpace ℂ
  -- (Fin (2^(8*colorDim 2))). Parametric integration in ℂ has a
  -- canonical topology and avoids an irrelevant PiLp instance choice.
  have hcoord (i : Fin (2 ^ (8 * colorDim 2))) (x : Boson 2) :
      (sourceHaarAverageRaw M G f x) i =
        ∫ g : GaugeGroup 2,
          (G.fermion g (f (G.boson g⁻¹ x))) i ∂sourceHaar := by
    change (∫ g : GaugeGroup 2,
        G.fermion g (f (G.boson g⁻¹ x)) ∂sourceHaar) i = _
    exact eval_integral_piLp
      (fun j => (sourceHaarIntegrand_integrable M G f x).eval_piLp j) i
  have hcoords : Continuous (fun x : Boson 2 =>
      (fun i : Fin (2 ^ (8 * colorDim 2)) =>
        (sourceHaarAverageRaw M G f x) i)) := by
    apply continuous_pi
    intro i
    -- Fix the source Fermion 2 coordinate projection's type before
    -- composing; otherwise PiLp/WithLp elaboration leaves metavariables.
    have hproj : Continuous (fun v : Fermion 2 => v i) :=
      PiLp.continuous_apply 2
        (fun _ : Fin (2 ^ (8 * colorDim 2)) => ℂ) i
    have hjoint : Continuous (fun p : Boson 2 × GaugeGroup 2 =>
        (G.fermion p.2 (f (G.boson p.2⁻¹ p.1))) i) :=
      hproj.comp (sourceHaarIntegrand_jointContinuous M G f)
    have hscalar := continuous_parametric_integral_of_continuous
      (μ := sourceHaar)
      (f := fun x : Boson 2 => fun g : GaugeGroup 2 =>
        (G.fermion g (f (G.boson g⁻¹ x))) i)
      (s := Set.univ) hjoint isCompact_univ
    have hc : Continuous (fun x : Boson 2 =>
        ∫ g : GaugeGroup 2,
          (G.fermion g (f (G.boson g⁻¹ x))) i ∂sourceHaar) := by
      simpa only [MeasureTheory.setIntegral_univ] using hscalar
    have heq :
        (fun x : Boson 2 => (sourceHaarAverageRaw M G f x) i) =
        (fun x : Boson 2 =>
          ∫ g : GaugeGroup 2,
            (G.fermion g (f (G.boson g⁻¹ x))) i ∂sourceHaar) := by
      funext x
      exact hcoord i x
    rw [heq]
    exact hc
  -- Assemble the same finitely indexed coordinates with the genuine
  -- source PiLp product topology, not a surrogate metric-space instance.
  change Continuous (fun x : Boson 2 =>
    WithLp.toLp 2 (fun i : Fin (2 ^ (8 * colorDim 2)) =>
      (sourceHaarAverageRaw M G f x) i))
  exact (PiLp.continuous_toLp 2
    (fun _ : Fin (2 ^ (8 * colorDim 2)) => ℂ)).comp hcoords

/-- Compact gauge saturation of the ACTUAL source smooth test
function's support. No averaging-space compactness assumption. -/
private def sourceGaugeSaturatedSupport (f : SmoothCore 2) : Set (Boson 2) :=
  (fun p : GaugeGroup 2 × Boson 2 => G.boson p.1 p.2) ''
    (Set.univ ×ˢ tsupport (f : Boson 2 → Fermion 2))

private theorem sourceGaugeSaturatedSupport_isCompact (f : SmoothCore 2) :
    IsCompact (sourceGaugeSaturatedSupport M G f) := by
  exact (isCompact_univ.prod f.hasCompactSupport).image G.boson_continuous

/-- The raw true-source Haar average has compact support.
This uses the compact orbit of support under the real orthogonal
source gauge action and no smoothness hypothesis on the average. -/
theorem sourceHaarAverageRaw_hasCompactSupport (f : SmoothCore 2) :
    HasCompactSupport (sourceHaarAverageRaw M G f) := by
  let K := sourceGaugeSaturatedSupport M G f
  have hc : IsCompact K := sourceGaugeSaturatedSupport_isCompact M G f
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro x hx
  by_contra hnotK
  have hvanish (g : GaugeGroup 2) :
      f (G.boson g⁻¹ x) = 0 := by
    by_contra hf
    have hs : G.boson g⁻¹ x ∈ tsupport (f : Boson 2 → Fermion 2) := by
      apply subset_closure
      simpa only [Function.mem_support] using hf
    have hp : (g, G.boson g⁻¹ x) ∈
        Set.univ ×ˢ tsupport (f : Boson 2 → Fermion 2) :=
      ⟨Set.mem_univ _, hs⟩
    have himage : G.boson g (G.boson g⁻¹ x) ∈ K :=
      Set.mem_image_of_mem _ hp
    have hcancel : G.boson g (G.boson g⁻¹ x) = x := by
      simp
    exact hnotK (hcancel ▸ himage)
  have heq : sourceHaarAverageRaw M G f x = 0 := by
    change (∫ g : GaugeGroup 2,
      G.fermion g (f (G.boson g⁻¹ x)) ∂sourceHaar) = 0
    have hz :
        (fun g : GaugeGroup 2 => G.fermion g (f (G.boson g⁻¹ x))) =
          (fun _ : GaugeGroup 2 => (0 : Fermion 2)) := by
      funext g
      rw [hvanish g]
      simp
    rw [hz]
    simp
  exact (Function.mem_support.mp hx) heq

#print axioms sourceHaarIntegrand_jointContinuous
#print axioms sourceHaarAverageRaw_continuous
#print axioms sourceHaarAverageRaw_hasCompactSupport

end
end FCP.BFSSSU2PhysicalDomainD2B2
