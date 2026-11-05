import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52C2EOriginalNativeGaugeCliffordUnitHomProbe

/-!
S1V52-S2 — STAGED RESEARCH CANDIDATE for the exact original 48-real
Clifford EVEN-SUBALGEBRA membership of all positive-i quaternion
bivectors and native GaugeGroup 2 Clifford polynomial units.

This uses the precise pinned Mathlib `CliffordAlgebra.even Q`, whose
underlying submodule is `CliffordAlgebra.evenOdd Q 0`. Each bivector is
a product of two GENUINE original 48-source majorana generators,
certified by `CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero`; the full
quaternion polynomial follows by ℝ-linear closure.

This is NOT a Spin proof: Clifford star-unitary and
`lipschitzGroup Q` membership are separate obligations.
Uncompiled and unaccepted until strict pinned CI with #print axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 420000

namespace FCP.BFSSS1V52S2
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V6
open FCP.BFSSS1V52A
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52B2
open FCP.BFSSS1V52B3
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52C2E

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev Ev := CliffordAlgebra.evenOdd Q 0

/-- Original 48-source Z bivector belongs to the genuine even subalgebra. -/
theorem sourceZBivector_mem_even (α : RealSpinBlock) :
    sourceZBivector α ∈ CliffordAlgebra.even Q := by
  change CliffordAlgebra.ι Q (sourceBlockColorAxis α 0) *
      CliffordAlgebra.ι Q (sourceBlockColorAxis α 1) ∈ Ev
  exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q _ _

/-- Original 48-source Y bivector belongs to the genuine even subalgebra. -/
theorem sourceYBivector_mem_even (α : RealSpinBlock) :
    sourceYBivector α ∈ CliffordAlgebra.even Q := by
  change CliffordAlgebra.ι Q (sourceBlockColorAxis α 2) *
      CliffordAlgebra.ι Q (sourceBlockColorAxis α 0) ∈ Ev
  exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q _ _

/-- Original 48-source X bivector belongs to the genuine even subalgebra. -/
theorem sourceXBivector_mem_even (α : RealSpinBlock) :
    sourceXBivector α ∈ CliffordAlgebra.even Q := by
  change CliffordAlgebra.ι Q (sourceBlockColorAxis α 1) *
      CliffordAlgebra.ι Q (sourceBlockColorAxis α 2) ∈ Ev
  exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q _ _

/-- Every real original 48-Clifford source quaternion polynomial
(not only normalized ones) is actually in pinned Mathlib's even Q. -/
theorem sourceCliffordQuaternion_mem_even (α : RealSpinBlock)
    (p : SourceQuaternionCoords) :
    sourceCliffordQuaternion α p ∈ CliffordAlgebra.even Q := by
  have hone : (1 : C) ∈ Ev :=
    (CliffordAlgebra.even Q).one_mem
  have hz : sourceZBivector α ∈ Ev :=
    sourceZBivector_mem_even α
  have hy : sourceYBivector α ∈ Ev :=
    sourceYBivector_mem_even α
  have hx : sourceXBivector α ∈ Ev :=
    sourceXBivector_mem_even α
  change
    p.a • (1 : C) +
      p.b • sourceZBivector α +
      p.c • sourceYBivector α +
      p.d • sourceXBivector α ∈ Ev
  exact Ev.add_mem
    (Ev.add_mem
      (Ev.add_mem (Ev.smul_mem p.a hone) (Ev.smul_mem p.b hz))
      (Ev.smul_mem p.c hy))
    (Ev.smul_mem p.d hx)

/-- The already-qualified native GaugeGroup 2 to original Clifford
UNITS homomorphism has values in genuine Clifford even Q. Still
not enough to infer Mathlib spinGroup Q membership. -/
theorem originalNativeGaugeSourceCliffordUnitHom_mem_even
    (α : RealSpinBlock) (g : OAI.BFSSQuantum.GaugeGroup 2) :
    ((originalNativeGaugeSourceCliffordUnitHom α g : Cˣ) : C) ∈
      CliffordAlgebra.even Q := by
  rw [originalNativeGaugeSourceCliffordUnitHom_coe]
  exact sourceCliffordQuaternion_mem_even α
    (originalNativeQuaternionCoords g)

#print axioms sourceZBivector_mem_even
#print axioms sourceYBivector_mem_even
#print axioms sourceXBivector_mem_even
#print axioms sourceCliffordQuaternion_mem_even
#print axioms originalNativeGaugeSourceCliffordUnitHom_mem_even

end
end FCP.BFSSS1V52S2
