import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10DDDerivativeRangeGammaLieHom
import Mathlib.Geometry.Manifold.ChartedSpace

/-! F10DE: translate the actual source identity chart over the original topological group.
Expose literal chart and inverse functions, source/target sets and transition domains, then
collect the covering family in a named ChartedSpace value for the existing topology.
No global charted-space instance, smooth compatibility, IsManifold, tangent identification,
Lie-group structure or representation manifold differential is asserted.
Candidate until complete strict compilation and independent topology/type/axiom audit. -/
set_option autoImplicit false
namespace FCP.BFSSPairedSpin9Clifford
noncomputable section
open OAI.BFSSQuantum
open scoped Topology Matrix.Norms.Elementwise

local instance f10deLocalNormedAddCommGroup :
    NormedAddCommGroup (CliffordAlgebra source9Quadratic) := source9PBWNormedAddCommGroup
local instance f10deLocalNormedSpace :
    NormedSpace ℝ (CliffordAlgebra source9Quadratic) := source9PBWNormedSpace
local instance f10deLocalTopologicalGroup : IsTopologicalGroup (spinGroup source9Quadratic) :=
  source9Spin_isTopologicalGroup_pbw

/-- Left translate the same accepted identity chart, with unchanged inherited source topology. -/
noncomputable def source9SpinLeftTranslatedChart (g : spinGroup source9Quadratic) :
    OpenPartialHomeomorph (spinGroup source9Quadratic) (Fin 36 → ℝ) :=
  (Homeomorph.mulLeft g⁻¹).transOpenPartialHomeomorph source9SpinIdentityLocalChart

theorem source9SpinLeftTranslatedChart_source (g : spinGroup source9Quadratic) :
    (source9SpinLeftTranslatedChart g).source =
      (fun h : spinGroup source9Quadratic => g⁻¹ * h) ⁻¹' source9SpinIdentityLocalChart.source := rfl

theorem source9SpinLeftTranslatedChart_target (g : spinGroup source9Quadratic) :
    (source9SpinLeftTranslatedChart g).target = source9SpinIdentityLocalChart.target := rfl

theorem source9SpinLeftTranslatedChart_apply (g h : spinGroup source9Quadratic) :
    source9SpinLeftTranslatedChart g h = source9SpinIdentityLocalChart (g⁻¹ * h) := rfl

theorem source9SpinLeftTranslatedChart_symm_apply
    (g : spinGroup source9Quadratic) (t : Fin 36 → ℝ) :
    (source9SpinLeftTranslatedChart g).symm t = g * source9OrderedStrictPlaneWord t :=
  congrArg (fun h : spinGroup source9Quadratic => h * source9OrderedStrictPlaneWord t) (inv_inv g)

theorem source9SpinLeftTranslatedChart_self_mem_source (g : spinGroup source9Quadratic) :
    g ∈ (source9SpinLeftTranslatedChart g).source := by
  simpa only [source9SpinLeftTranslatedChart_source, Set.mem_preimage, inv_mul_cancel]
    using source9SpinIdentityLocalChart_one_mem_source

theorem source9SpinLeftTranslatedChart_self (g : spinGroup source9Quadratic) :
    source9SpinLeftTranslatedChart g g = 0 :=
  (congrArg (fun h : spinGroup source9Quadratic => source9SpinIdentityLocalChart h)
    (inv_mul_cancel g)).trans source9SpinIdentityLocalChart_one

/-- A covering topological atlas value; no global instance or smoothness data is installed. -/
@[instance_reducible]
noncomputable def source9SpinTranslatedChartedSpace :
    ChartedSpace (Fin 36 → ℝ) (spinGroup source9Quadratic) where
  atlas := Set.range source9SpinLeftTranslatedChart
  chartAt := source9SpinLeftTranslatedChart
  mem_chart_source := source9SpinLeftTranslatedChart_self_mem_source
  chart_mem_atlas g := ⟨g, rfl⟩

/-- Total transition function formula, separate from its restricted source domain and regularity. -/
theorem source9SpinLeftTranslatedChart_transition_apply
    (g h : spinGroup source9Quadratic) (t : Fin 36 → ℝ) :
    source9SpinLeftTranslatedChart g ((source9SpinLeftTranslatedChart h).symm t) =
      source9SpinIdentityLocalChart (g⁻¹ * (h * source9OrderedStrictPlaneWord t)) :=
  (source9SpinLeftTranslatedChart_apply g _).trans
    (congrArg (fun k : spinGroup source9Quadratic => source9SpinIdentityLocalChart (g⁻¹ * k))
      (source9SpinLeftTranslatedChart_symm_apply h t))

/-- The exact overlap source for transition from h-coordinates to g-coordinates. -/
theorem source9SpinLeftTranslatedChart_transition_source
    (g h : spinGroup source9Quadratic) :
    ((source9SpinLeftTranslatedChart h).symm.trans (source9SpinLeftTranslatedChart g)).source =
      source9SpinIdentityLocalChart.target ∩
        (fun t : Fin 36 → ℝ => g⁻¹ * (h * source9OrderedStrictPlaneWord t)) ⁻¹'
          source9SpinIdentityLocalChart.source := by
  ext t
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    source9SpinLeftTranslatedChart_target, source9SpinLeftTranslatedChart_source,
    Set.mem_inter_iff, Set.mem_preimage, source9SpinLeftTranslatedChart_symm_apply]

#print axioms source9SpinLeftTranslatedChart
#print axioms source9SpinLeftTranslatedChart_source
#print axioms source9SpinLeftTranslatedChart_target
#print axioms source9SpinLeftTranslatedChart_apply
#print axioms source9SpinLeftTranslatedChart_symm_apply
#print axioms source9SpinLeftTranslatedChart_self_mem_source
#print axioms source9SpinLeftTranslatedChart_self
#print axioms source9SpinTranslatedChartedSpace
#print axioms source9SpinLeftTranslatedChart_transition_apply
#print axioms source9SpinLeftTranslatedChart_transition_source
end
end FCP.BFSSPairedSpin9Clifford
