import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8BEOriginalNormalizedPhysicalHamiltonianProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD1RestrictedSourceGraphProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K2BNonzeroPhysicalL2Probe

/-!
# H5E8BF — exact original/legacy SU2 charge graph crosswalk and paired source H

PROSPECTIVE, UNQUALIFIED until strict pinned CI and permitted-axiom audit.

AY's ORIGINAL invariant SmoothCore graph is defined using
M.chargeVector, not the deformed charge. Separately, qualified D1
identified G.deformedModelGraph at (h,m)=(1,0) with the same original
invariant-core closure. We prove that typed equality explicitly and
transport it to the ACTUAL AY physical-input / PiLp16-output graph.

We then specialize the newly BE-qualified actual source Hamiltonian
H=(1/16)T†T to the real pairedAlgebraData / pairedGaugeData SU2
24-boson 48-Majorana Fock realization, with its known nonzero true
gauge-invariant physical Hilbert space. True self-adjointness,
unchanged source domain and exact weak-form characterization are
rechecked for this concrete representation.

This source graph equality does NOT itself import/requalify the distinct
historical D2B17/D2B28 Hilbert partial-operator declarations: equality
of their EXACT typed operators remains a follow-on proof obligation.
Nor does it prove the independent paper Cl(48)/Spin(48) representation,
positive eigenvalues, or an SU2 BFSS mass gap.
-/

set_option autoImplicit false
set_option maxHeartbeats 220000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8BF
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AU
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open FCP.BFSSSU2PhysicalDomainL6H5E8BC
open FCP.BFSSSU2PhysicalDomainL6H5E8BE
open FCP.BFSSSU2PhysicalDomainD1
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2GaugeG4K2B

/-- The true original M.chargeVector invariant-core closure IS the
literal source's own gauge-restricted deformedModelGraph(1,0). This
uses D1's exact kernel-qualified source-charge identity, not any
unverified maximal differential operator or manuscript alias. -/
theorem originalMinimalClosedGraph_eq_exactSourceGaugeGraph
    {N : ℕ} (M : AlgebraData N) (G : M.GaugeData) :
    originalMinimalClosedGraph M G = G.deformedModelGraph 1 0 := by
  calc
    originalMinimalClosedGraph M G =
        originalRestrictedClosedGraph M G := rfl
    _ = G.deformedModelGraph 1 0 :=
        (sourceGaugeRestrictedClosedGraph_equal M G).symm

/-- Membership in the ACTUAL original AY Hilbert charge graph is
exactly membership in the separately accepted pinned source gauge
graph after canonical physical inclusion and PiLp(2) identification. -/
theorem originalMinimalPhysicalHilbertChargeGraph_mem_source_iff
    {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)
    (p : G.physicalSpace × PiLp 2 (fun _ : SpinIndex => FullL2 N)) :
    p ∈ originalMinimalPhysicalHilbertChargeGraph M G ↔
      ((p.1 : FullL2 N), originalMinimalHilbertOutputEquiv p.2) ∈
        G.deformedModelGraph 1 0 := by
  rw [originalMinimalPhysicalHilbertChargeGraph_mem_iff M G p,
    originalMinimalClosedGraph_eq_exactSourceGaugeGraph M G]

/-- The original AY graph equals the genuinely original source
gauge-restricted (1,0) graph rebased to EXACTLY the native physical
Hilbert input and sixteen-component Hilbert output. -/
theorem originalMinimalPhysicalHilbertChargeGraph_eq_sourceRebased
    {N : ℕ} (M : AlgebraData N) (G : M.GaugeData) :
    originalMinimalPhysicalHilbertChargeGraph M G =
      (G.deformedModelGraph 1 0).comap
        (G.physicalSpace.subtype.prodMap
          (originalMinimalHilbertOutputEquiv (N := N)).toLinearMap) := by
  unfold originalMinimalPhysicalHilbertChargeGraph
  rw [originalMinimalClosedGraph_eq_exactSourceGaugeGraph M G]

/-- An equality of the TRUE original partial-operator graph to that
source-rebased graph, not merely a dense-core/form coincidence. -/
theorem originalMinimalPhysicalHilbertChargeColumn_graph_eq_sourceRebased
    {N : ℕ} (M : AlgebraData N) (G : M.GaugeData) :
    (originalMinimalPhysicalHilbertChargeColumn M G).graph =
      (G.deformedModelGraph 1 0).comap
        (G.physicalSpace.subtype.prodMap
          (originalMinimalHilbertOutputEquiv (N := N)).toLinearMap) := by
  rw [originalMinimalPhysicalHilbertChargeColumn_graph_eq,
      originalMinimalPhysicalHilbertChargeGraph_eq_sourceRebased]

/-- The concrete paired original BFSS SU2 normalized operator.
No change to the source charge/gamma/gauge sign or Hilbert domain. -/
noncomputable def pairedOriginalPhysicalNormalizedHamiltonian :
    pairedGaugeData.physicalSpace →ₗ.[ℂ] pairedGaugeData.physicalSpace :=
  originalMinimalPhysicalNormalizedHamiltonian
    pairedAlgebraData pairedGaugeData

/-- Actual, nontrivial physical Hilbert space in the paired 48-Majorana
and 24-boson realization, not merely an abstract nonempty ambient. -/
theorem pairedOriginalPhysicalSpace_ne_bot :
    pairedGaugeData.physicalSpace ≠ (⊥ : Submodule ℂ (FullL2 2)) :=
  pairedPhysicalSpace_ne_bot

/-- The ACTUAL original AY/BE paired SU2 Hamiltonian is self-adjoint. -/
theorem pairedOriginalPhysicalNormalizedHamiltonian_selfAdjoint :
    letI : CompleteSpace pairedGaugeData.physicalSpace :=
      originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
    IsSelfAdjoint pairedOriginalPhysicalNormalizedHamiltonian := by
  let : CompleteSpace pairedGaugeData.physicalSpace :=
    originalPhysicalHilbertComplete pairedAlgebraData pairedGaugeData
  exact originalMinimalPhysicalNormalizedHamiltonian_selfAdjoint
    pairedAlgebraData pairedGaugeData

/-- In the concrete source gauge model, the Hamiltonian has
exactly the unscaled T†T natural domain. -/
theorem pairedOriginalPhysicalNormalizedHamiltonian_domain :
    pairedOriginalPhysicalNormalizedHamiltonian.domain =
      (originalMinimalPhysicalHilbertChargeAdjointSquare
        pairedAlgebraData pairedGaugeData).domain := by
  exact originalMinimalPhysicalNormalizedHamiltonian_domain
    pairedAlgebraData pairedGaugeData

/-- Concrete paired true physical weak-form representation, keeping
all sixteen original charge outputs and the exact 1/16 factor. -/
theorem pairedOriginalPhysicalNormalizedHamiltonian_weakForm_iff
    (u : (originalMinimalPhysicalHilbertChargeColumn
      pairedAlgebraData pairedGaugeData).domain)
    (w : pairedGaugeData.physicalSpace) :
    (∀ v : (originalMinimalPhysicalHilbertChargeColumn
        pairedAlgebraData pairedGaugeData).domain,
      inner ℂ w (v : pairedGaugeData.physicalSpace) =
        (1 / 16 : ℂ) *
          inner ℂ (originalMinimalPhysicalHilbertChargeColumn
            pairedAlgebraData pairedGaugeData u)
            (originalMinimalPhysicalHilbertChargeColumn
              pairedAlgebraData pairedGaugeData v)) ↔
      ∃ h : (u : pairedGaugeData.physicalSpace) ∈
          pairedOriginalPhysicalNormalizedHamiltonian.domain,
        w = pairedOriginalPhysicalNormalizedHamiltonian ⟨u, h⟩ := by
  exact originalMinimalPhysicalNormalizedHamiltonian_weakForm_iff
    pairedAlgebraData pairedGaugeData u w

#print axioms originalMinimalClosedGraph_eq_exactSourceGaugeGraph
#print axioms originalMinimalPhysicalHilbertChargeGraph_mem_source_iff
#print axioms originalMinimalPhysicalHilbertChargeGraph_eq_sourceRebased
#print axioms originalMinimalPhysicalHilbertChargeColumn_graph_eq_sourceRebased
#print axioms pairedOriginalPhysicalNormalizedHamiltonian
#print axioms pairedOriginalPhysicalSpace_ne_bot
#print axioms pairedOriginalPhysicalNormalizedHamiltonian_selfAdjoint
#print axioms pairedOriginalPhysicalNormalizedHamiltonian_domain
#print axioms pairedOriginalPhysicalNormalizedHamiltonian_weakForm_iff

end
end FCP.BFSSSU2PhysicalDomainL6H5E8BF
