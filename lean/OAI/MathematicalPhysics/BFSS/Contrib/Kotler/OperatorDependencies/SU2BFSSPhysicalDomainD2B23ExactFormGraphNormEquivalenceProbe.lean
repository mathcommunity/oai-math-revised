import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B22ExactHilbertEnergyFormTransportProbe

/-!
# BFSS SU2 D2B23 — exact closed Hilbert graph and normalized form norm comparison

PROSPECTIVE until exact pinned Lean 4.34.1 Actions kernel/axioms PASS.

Let T be the true source-derived, closed, densely defined physical
sixteen-component Hilbert charge column. Gate D2B22 already establishes
q(ψ) = (1/16) ‖Tψ‖² and its exact original BFSS source correspondence.

Here the actual Hilbert graph is proved CompleteSpace, and the literal
squared form norm F(ψ) = ‖ψ‖² + q(ψ) is bounded against the
graph squared norm G(ψ) = ‖ψ‖² + ‖Tψ‖²:

  F(ψ) ≤ G(ψ) ≤ 16 F(ψ).

This is the crucial norm-equivalence estimate for the closed form.
Do NOT claim an abstract form-representation theorem or an associated
Hamiltonian operator merely from these estimates.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B23
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B17
open FCP.BFSSSU2PhysicalDomainD2B22

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- Complete graph of the ACTUAL original source physical Hilbert charge,
from its previously verified closedness and Hilbert completeness. -/
theorem sourcePhysicalHilbertCharge_graph_complete :
    CompleteSpace ((sourcePhysicalHilbertChargeColumn M G).graph) := by
  let : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  let : _root_.IsClosed
      ((sourcePhysicalHilbertChargeColumn M G).graph :
        Set (G.physicalSpace × SourceChargeHilbertOutput)) :=
    sourcePhysicalHilbertChargeColumn_isClosed M G
  infer_instance

/-- The literal squared norm of the source-normalized closed physical
charge form, with the exact 1/16 coefficient from D2B22. -/
noncomputable def sourcePhysicalFormNormSq
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) : ℝ :=
  ‖(u : G.physicalSpace)‖ ^ 2 + sourcePhysicalHilbertChargeEnergy M G u

/-- The ordinary graph squared norm of the same exact source column. -/
noncomputable def sourcePhysicalGraphNormSq
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) : ℝ :=
  ‖(u : G.physicalSpace)‖ ^ 2 +
    ‖sourcePhysicalHilbertChargeColumn M G u‖ ^ 2

theorem sourcePhysicalFormNormSq_nonneg
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) :
    0 ≤ sourcePhysicalFormNormSq M G u := by
  exact add_nonneg (sq_nonneg _)
    (sourcePhysicalHilbertChargeEnergy_nonneg M G u)

theorem sourcePhysicalFormNormSq_le_graph
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) :
    sourcePhysicalFormNormSq M G u ≤
      sourcePhysicalGraphNormSq M G u := by
  unfold sourcePhysicalFormNormSq sourcePhysicalGraphNormSq
    sourcePhysicalHilbertChargeEnergy
  have h : 0 ≤ ‖sourcePhysicalHilbertChargeColumn M G u‖ ^ 2 :=
    sq_nonneg _
  nlinarith

theorem sourcePhysicalGraphNormSq_le_sixteen_form
    (u : (sourcePhysicalHilbertChargeColumn M G).domain) :
    sourcePhysicalGraphNormSq M G u ≤
      16 * sourcePhysicalFormNormSq M G u := by
  unfold sourcePhysicalFormNormSq sourcePhysicalGraphNormSq
    sourcePhysicalHilbertChargeEnergy
  have h : 0 ≤ ‖(u : G.physicalSpace)‖ ^ 2 := sq_nonneg _
  nlinarith

#print axioms sourcePhysicalHilbertCharge_graph_complete
#print axioms sourcePhysicalFormNormSq_nonneg
#print axioms sourcePhysicalFormNormSq_le_graph
#print axioms sourcePhysicalGraphNormSq_le_sixteen_form

end
end FCP.BFSSSU2PhysicalDomainD2B23
