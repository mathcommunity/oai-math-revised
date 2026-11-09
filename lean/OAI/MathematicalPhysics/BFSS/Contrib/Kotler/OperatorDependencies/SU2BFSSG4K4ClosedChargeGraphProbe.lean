import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K3NonzeroSmoothInvariantCoreProbe

/-!
# BFSS SU(2) G4-K4 — exact closed supercharge-graph domain for a physical state

Gate #132 certified a genuinely nonzero, smooth, compactly supported
invariant test section in the TRUE pinned SU(2) BFSS invariantCore,
whose coreToL2 image is the concrete Gate #130 nonzero physical state.

The pinned upstream AlgebraData.fullCoreGraph is the range of the
literal (coreToL2, chargeVector) map and fullClosedGraph its
topological closure. We prove that this particular nonzero Gauss
state belongs to the domain of THAT concrete closed supercharge
vector, identify the output and prove its uniqueness using the
upstream closability result. The output is evaluated with the
ACTUAL pairedAlgebraData.charge family.

We do NOT establish that supercharges preserve the Gauss space,
vanish on this vector, have a spectral gap, or admit a ground state.
-/

namespace FCP.BFSSSU2GaugeG4K4
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4K2B
open FCP.BFSSSU2GaugeG4K3

/-- Exact vector of 16 pinned BFSS supercharge images of the accepted
NONZERO smooth SU(2) Gauss-invariant state. -/
noncomputable def radialBumpChargeVector : SpinIndex → FullL2 2 :=
  pairedAlgebraData.chargeVector radialBumpSmoothCore

theorem radialBumpChargeVector_apply (α : SpinIndex) :
    radialBumpChargeVector α =
      coreToL2 (pairedAlgebraData.charge α radialBumpSmoothCore) := rfl

/-- The actual (physical state, charge-vector) pair lies in the
PINNED unsmoothed charge graph. No closed-graph limit is needed. -/
theorem radialBumpCoreGraph_mem :
    (radialBumpL2, radialBumpChargeVector) ∈
      pairedAlgebraData.fullCoreGraph := by
  change (radialBumpL2, radialBumpChargeVector) ∈
    LinearMap.range (coreToL2.prod pairedAlgebraData.chargeVector)
  rw [← radialBumpSmoothCore_toL2]
  change (coreToL2 radialBumpSmoothCore,
    pairedAlgebraData.chargeVector radialBumpSmoothCore) ∈
      LinearMap.range (coreToL2.prod pairedAlgebraData.chargeVector)
  exact ⟨radialBumpSmoothCore, rfl⟩

/-- The exact nonzero Gauss physical L² vector therefore belongs
to the domain of the concrete closed supercharge-vector relation. -/
theorem radialBumpClosedGraph_mem :
    (radialBumpL2, radialBumpChargeVector) ∈
      pairedAlgebraData.fullClosedGraph :=
  pairedAlgebraData.fullCoreGraph.le_topologicalClosure
    radialBumpCoreGraph_mem

/-- The output in the pinned closed supercharge graph is UNIQUE
for this nonzero physical state. This uses the upstream
fullClosedGraph_unique theorem, rather than a new axiom. -/
theorem radialBumpClosedGraph_unique
    (y : SpinIndex → FullL2 2)
    (hy : (radialBumpL2, y) ∈ pairedAlgebraData.fullClosedGraph) :
    y = radialBumpChargeVector :=
  pairedAlgebraData.fullClosedGraph_unique hy radialBumpClosedGraph_mem

/-- In particular a NONZERO physical state lies in the domain
of the actual closed supercharge vector. This is not a statement
about its eigenvalue or a zero-energy/supersymmetric vacuum. -/
theorem exists_nonzero_physical_closedGraph_witness :
    ∃ y : SpinIndex → FullL2 2,
      (radialBumpL2, y) ∈ pairedAlgebraData.fullClosedGraph ∧
        radialBumpL2 ≠ 0 :=
  ⟨radialBumpChargeVector, radialBumpClosedGraph_mem, radialBumpL2_ne_zero⟩

/-- The output obeys the exact upstream symmetric-charge pairing
against every smooth-core test function. -/
theorem radialBumpClosedGraph_pairing
    (α : SpinIndex) (f : SmoothCore 2) :
    inner ℂ (coreToL2 (pairedAlgebraData.charge α f)) radialBumpL2 =
      inner ℂ (coreToL2 f) (radialBumpChargeVector α) :=
  pairedAlgebraData.fullClosedGraph_pairing
    radialBumpClosedGraph_mem α f

/-- The exact quadratic form on our nonzero Gauss test state is
the sum of 16 squared norms of the TRUE charge-vector output.
This is a definitional identity, not a strict lower bound. -/
theorem radialBump_coreForm_charge_norm_identity :
    pairedAlgebraData.coreForm radialBumpSmoothCore =
      (1 / 16 : ℝ) *
        ∑ α : SpinIndex, ‖radialBumpChargeVector α‖ ^ 2 := rfl

#print axioms radialBumpChargeVector
#print axioms radialBumpChargeVector_apply
#print axioms radialBumpCoreGraph_mem
#print axioms radialBumpClosedGraph_mem
#print axioms radialBumpClosedGraph_unique
#print axioms exists_nonzero_physical_closedGraph_witness
#print axioms radialBumpClosedGraph_pairing
#print axioms radialBump_coreForm_charge_norm_identity

end
end FCP.BFSSSU2GaugeG4K4
