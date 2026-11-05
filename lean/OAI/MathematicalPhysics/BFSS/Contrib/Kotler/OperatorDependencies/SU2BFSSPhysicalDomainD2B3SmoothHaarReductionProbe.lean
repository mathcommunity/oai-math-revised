import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B2HaarAverageContinuitySupportProbe
import OAI.Analysis.VlasovMaxwell.Regularity.SmoothIntegral

/-!
# BFSS SU(2) D2B3 — spatial smoothness and exact analytic reduction

PROSPECTIVE / UNCOMPILED until dedicated pinned GitHub Actions gate passes.
The actual source gauge-average function is preserved unchanged.

This is NOT a proof that the Haar average itself is smooth.
The second theorem makes the remaining all-jet joint-continuity
obligation EXPLICIT in its hypotheses, rather than hiding it.
A genuine unconditional smoothness/density theorem must DISCHARGE
those hypotheses from source GaugeData before D2B completes.

Uses existing pinned OAI.RVM.contDiff_integral_smoothFamily, which
differentiates an integral over a compact, finite-measure parameter
space without requiring smoothness in the parameter itself.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B3
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open OAI.Laughlin.Rotation
open FCP.BFSSSU2PhysicalDomainD2B1
open FCP.BFSSSU2PhysicalDomainD2B2
open MeasureTheory
open scoped Topology ContDiff

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Each integrand at a FIXED actual source SU(2) gauge group element
is infinitely differentiable in the REAL bosonic position.
This uses actual source boson and fermion linear isometries,
including restriction of the complex fermion representation
to real scalars for spatial Fréchet differentiation. -/
theorem sourceHaarSpatialSlice_contDiff
    (f : SmoothCore 2) (g : GaugeGroup 2) :
    ContDiff ℝ ∞
      (fun x : Boson 2 =>
        G.fermion g (f (G.boson g⁻¹ x))) := by
  have hb : ContDiff ℝ ∞ (fun x : Boson 2 => G.boson g⁻¹ x) :=
    (G.boson g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  have hf : ContDiff ℝ ∞ (fun v : Fermion 2 => G.fermion g v) :=
    ((G.fermion g).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).contDiff
  exact hf.comp (f.contDiff.comp hb)

/-- EXACT remaining regularity criterion for the TRUE original
BFSS Haar average, reduced to continuity of the n-th spatial
Fréchet derivative jointly in bosonic position and source SU(2).

The hJets hypothesis is NOT established here, and MUST NOT be
promoted to a new GaugeData axiom or treated as accepted physics.
This is an analytical reduction, not the D2B density result. -/
theorem sourceHaarAverageRaw_contDiff_of_jointJets
    (f : SmoothCore 2)
    (hJets : ∀ n : ℕ,
      Continuous (fun p : Boson 2 × GaugeGroup 2 =>
        iteratedFDeriv ℝ n
          (fun x : Boson 2 =>
            G.fermion p.2 (f (G.boson p.2⁻¹ x))) p.1)) :
    ContDiff ℝ ∞ (sourceHaarAverageRaw M G f) := by
  have hFamily : OAI.RVM.SmoothCompactFamily
      (fun g : GaugeGroup 2 => fun x : Boson 2 =>
        G.fermion g (f (G.boson g⁻¹ x))) :=
    ⟨sourceHaarSpatialSlice_contDiff M G f, hJets⟩
  -- This is the exact original SU2 group: the subtype of a 2×2
  -- complex matrix product. Establish its STANDARD second-countability
  -- locally; do not extend GaugeData or postulate smoothness.
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  -- The actual source group is the standard subtype of the matrix
  -- product. Invoke the instance by its exact full Mathlib namespace;
  -- using inferInstance here left its own goal unresolved in Gate #19.
  haveI : SecondCountableTopology (GaugeGroup 2) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have h := OAI.RVM.contDiff_integral_smoothFamily
    (μ := sourceHaar) hFamily
  exact h

#print axioms sourceHaarSpatialSlice_contDiff
#print axioms sourceHaarAverageRaw_contDiff_of_jointJets

end
end FCP.BFSSSU2PhysicalDomainD2B3
