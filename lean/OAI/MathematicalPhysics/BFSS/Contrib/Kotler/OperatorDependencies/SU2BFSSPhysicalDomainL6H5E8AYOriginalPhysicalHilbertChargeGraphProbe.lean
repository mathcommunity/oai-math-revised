import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AXOriginalPhysicalHilbertParityUnitaryProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AWOriginalMinimalChargeHilbertFormParityProbe
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# H5E8AY — actual original minimal charge graph on the PHYSICAL Hilbert input

Construct directly from accepted AU original (not deformed) closed
source M.chargeVector gauge-invariant SmoothCore graph. Rebase:
 INPUT  = the genuine original G.physicalSpace SU2 gauge-invariant Hilbert subspace
 OUTPUT = the genuine PiLp 2 of all sixteen original FullL2 charges.

Source physical input membership follows by CLOSEDNESS of the true
source G.physicalSpace under limits of invariant SmoothCore states.
The restricted graph remains closed and single-valued, yielding an
ACTUAL Mathlib partial linear operator with its exact domain.

Caution: domain DENSITY in the physical Hilbert space is a DISTINCT
unproved obligation in this module. Neither closedness nor physical
parity proves density. No Hilbert adjoint, associated (1/16)T†T,
historical Gate93 operator alias, or manuscript spectral claim is
asserted. Keep this module independently source-pinned and axiom clean.
-/

set_option autoImplicit false
set_option maxHeartbeats 270000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AY
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AU
open FCP.BFSSSU2PhysicalDomainL6H5E8AW
open MeasureTheory Set
open scoped InnerProductSpace

/-- The literal original restricted minimal closed source charge graph
has only PHYSICAL inputs, since every original invariant-core source
input was already physical and the true source physical Hilbert
subspace is topologically closed. NOT a density assertion. -/
theorem originalMinimalClosedGraph_input_physical {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    {p : FullL2 N × (SpinIndex → FullL2 N)}
    (hp : p ∈ originalMinimalClosedGraph M G) :
    p.1 ∈ G.physicalSpace := by
  let X := FullL2 N × (SpinIndex → FullL2 N)
  have hclosed : IsClosed {q : X | q.1 ∈ G.physicalSpace} :=
    G.physicalSpace_closed.preimage continuous_fst
  have hcore :
      (originalMinimalCoreGraph M G : Set X) ⊆
        {q : X | q.1 ∈ G.physicalSpace} := by
    rintro q ⟨f,rfl⟩
    exact f.property
  have hclosure :
      closure (originalMinimalCoreGraph M G : Set X) ⊆
        {q : X | q.1 ∈ G.physicalSpace} :=
    closure_minimal hcore hclosed
  change p ∈ closure (originalMinimalCoreGraph M G : Set X) at hp
  exact hclosure hp

/-- The exact finite sixteen-output Hilbert sum's canonical continuous
linear identification with the original source SpinIndex function
type; no changed source charge. -/
noncomputable def originalMinimalHilbertOutputEquiv {N : ℕ} :
    (PiLp 2 (fun _ : SpinIndex => FullL2 N)) ≃L[ℂ]
      (SpinIndex → FullL2 N) :=
  PiLp.continuousLinearEquiv 2 ℂ (fun _ : SpinIndex => FullL2 N)

/-- Exact source original minimal CLOSED charge graph, now rebased
onto BOTH its actual physical input Hilbert space and genuine finite
Hilbert output, not the older deformed source operator. -/
noncomputable def originalMinimalPhysicalHilbertChargeGraph {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    Submodule ℂ (G.physicalSpace ×
      PiLp 2 (fun _ : SpinIndex => FullL2 N)) :=
  (originalMinimalClosedGraph M G).comap
    (G.physicalSpace.subtype.prodMap
      (originalMinimalHilbertOutputEquiv (N := N)).toLinearMap)

/-- Membership is literally the accepted original source minimal
closed charge graph after the canonical physical input inclusion and
canonical Hilbert-output coordinate homeomorphism. -/
theorem originalMinimalPhysicalHilbertChargeGraph_mem_iff {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (p : G.physicalSpace × PiLp 2 (fun _ : SpinIndex => FullL2 N)) :
    p ∈ originalMinimalPhysicalHilbertChargeGraph M G ↔
      ((p.1 : FullL2 N), originalMinimalHilbertOutputEquiv p.2) ∈
        originalMinimalClosedGraph M G := by
  rfl

/-- Original pinned fullClosedGraph vertical uniqueness passes through
physical-input rebasing and the genuine sixteen-output Hilbert
equivalence. This gives an ACTUAL single-valued unbounded operator. -/
private theorem originalMinimalPhysicalHilbertChargeGraph_vertical {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    ∀ p : G.physicalSpace × PiLp 2 (fun _ : SpinIndex => FullL2 N),
      p ∈ originalMinimalPhysicalHilbertChargeGraph M G →
      p.1 = 0 → p.2 = 0 := by
  rintro ⟨u,y⟩ hp hu
  have hsrc :
      ((u : FullL2 N), originalMinimalHilbertOutputEquiv y) ∈
        originalMinimalClosedGraph M G :=
    (originalMinimalPhysicalHilbertChargeGraph_mem_iff M G _).mp hp
  dsimp at hu
  subst u
  have hzero : originalMinimalHilbertOutputEquiv y = 0 :=
    M.fullClosedGraph_vertical
      (originalMinimalClosedGraph_le_full M G hsrc)
  apply (originalMinimalHilbertOutputEquiv (N := N)).injective
  simpa using hzero

/-- TRUE ORIGINAL minimal closed unbounded charge operator on the
correct physical Hilbert input and true sixteen-output Hilbert sum.
It is NOT an assumed extension or D2B12 source-model alias. -/
noncomputable def originalMinimalPhysicalHilbertChargeColumn {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    G.physicalSpace →ₗ.[ℂ]
      PiLp 2 (fun _ : SpinIndex => FullL2 N) :=
  (originalMinimalPhysicalHilbertChargeGraph M G).toLinearPMap

/-- The exact native Mathlib graph is that original minimal source
physical Hilbert graph, without extra closure or a proxy operator. -/
theorem originalMinimalPhysicalHilbertChargeColumn_graph_eq {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    (originalMinimalPhysicalHilbertChargeColumn M G).graph =
      originalMinimalPhysicalHilbertChargeGraph M G := by
  exact Submodule.toLinearPMap_graph_eq _
    (originalMinimalPhysicalHilbertChargeGraph_vertical M G)

/-- The ACTUAL physical-input, PiLp-two-output original minimal charge
operator is closed in the correct physical Hilbert-product topology.
This is not the same as proving its physical-domain density. -/
theorem originalMinimalPhysicalHilbertChargeColumn_isClosed {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData) :
    (originalMinimalPhysicalHilbertChargeColumn M G).IsClosed := by
  change IsClosed ((originalMinimalPhysicalHilbertChargeColumn M G).graph :
    Set (G.physicalSpace × PiLp 2 (fun _ : SpinIndex => FullL2 N)))
  rw [originalMinimalPhysicalHilbertChargeColumn_graph_eq M G]
  change IsClosed {p : G.physicalSpace × PiLp 2
      (fun _ : SpinIndex => FullL2 N) |
    ((p.1 : FullL2 N), originalMinimalHilbertOutputEquiv p.2) ∈
      (originalMinimalClosedGraph M G :
        Set (FullL2 N × (SpinIndex → FullL2 N)))}
  have hc : IsClosed (originalMinimalClosedGraph M G :
      Set (FullL2 N × (SpinIndex → FullL2 N))) :=
    (originalMinimalCoreGraph M G).isClosed_topologicalClosure
  have hf : Continuous (fun p : G.physicalSpace × PiLp 2
      (fun _ : SpinIndex => FullL2 N) =>
      ((p.1 : FullL2 N), originalMinimalHilbertOutputEquiv p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((originalMinimalHilbertOutputEquiv).continuous.comp continuous_snd)
  exact hc.preimage hf

/-- Domain of the ACTUAL physical-Hilbert operator is EXACTLY the
original AU minimal closed charge domain intersected with the physical
Hilbert input subtype; the original closed graph proves this is not an
arbitrary new extension. NOT a claim that this domain is dense. -/
theorem originalMinimalPhysicalHilbertChargeColumn_domain_iff {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (u : G.physicalSpace) :
    u ∈ (originalMinimalPhysicalHilbertChargeColumn M G).domain ↔
      (u : FullL2 N) ∈ (originalMinimalClosedChargeColumn M G).domain := by
  constructor
  · intro hu
    obtain ⟨y,hy⟩ := (LinearPMap.mem_domain_iff).mp hu
    rw [originalMinimalPhysicalHilbertChargeColumn_graph_eq M G] at hy
    have hp : ((u : FullL2 N), originalMinimalHilbertOutputEquiv y) ∈
        originalMinimalClosedGraph M G :=
      (originalMinimalPhysicalHilbertChargeGraph_mem_iff M G _).mp hy
    apply LinearPMap.mem_domain_of_mem_graph
    rwa [originalMinimalClosedChargeColumn_graph_eq M G]
  · intro hu
    obtain ⟨y,hy⟩ := (LinearPMap.mem_domain_iff).mp hu
    rw [originalMinimalClosedChargeColumn_graph_eq M G] at hy
    apply LinearPMap.mem_domain_of_mem_graph
    rw [originalMinimalPhysicalHilbertChargeColumn_graph_eq M G]
    apply (originalMinimalPhysicalHilbertChargeGraph_mem_iff M G _).mpr
    have hout : originalMinimalHilbertOutputEquiv (WithLp.toLp 2 y) = y := by
      rfl
    rw [hout]
    exact hy

#print axioms originalMinimalClosedGraph_input_physical
#print axioms originalMinimalHilbertOutputEquiv
#print axioms originalMinimalPhysicalHilbertChargeGraph
#print axioms originalMinimalPhysicalHilbertChargeGraph_mem_iff
#print axioms originalMinimalPhysicalHilbertChargeColumn
#print axioms originalMinimalPhysicalHilbertChargeColumn_graph_eq
#print axioms originalMinimalPhysicalHilbertChargeColumn_isClosed
#print axioms originalMinimalPhysicalHilbertChargeColumn_domain_iff

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AY
