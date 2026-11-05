import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10KSourceEigenvalueCardinalityBalanceProbe
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
V10H-F10L — original real gamma source EXACT EIGHT/EIGHT spectral multiplicity.

F10J strictly qualified a partition of the original SpinIndex labels
into positive/negative sqrt(Q) eigenvalue filters for nonzero nine-vectors.
F10K strictly qualified equality of the exact Nat filter cardinalities.
Pinned original BFSS Core defines SpinIndex := Fin 16, not a proxy.

This module tests three exact type-level obligations:
1. original SpinIndex has Fintype cardinality 16;
2. the ACTUAL positive-root source eigenvalue filter has cardinality 8;
3. the ACTUAL negative-root source eigenvalue filter has cardinality 8.

The source original gamma16 determinant sign is STILL NOT proved here:
that requires an independent exact source eigenvalue product derivation,
the positive/negative finite product partition, pow and Real.sqrt algebra,
and v=0 boundary. Global original SO48 and Spin48 lift remain separate.

No private gamma-table access, surrogate labels, new axioms, additional
limits, or modified accepted ancestors. F10L unqualified until strict
warning-as-error compilation and independent exact type+axiom audits PASS.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9DetFixture
noncomputable section

open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9Clifford
open FCP.BFSSS1V0
open OAI.BFSSQuantum
open Matrix

/-- Exact source BFSS spinor index, not 48-label Fock/color-major order. -/
theorem source9SpinIndex_card_sixteen :
    Fintype.card SpinIndex = 16 := by
  change Fintype.card (Fin 16) = 16
  exact Fintype.card_fin 16

/-- For each nonzero original nine-vector, EXACTLY eight source
spinor-index eigenvalues equal the positive real square-root. -/
theorem source9PositiveEigenIndices_card_eight
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) :
    (source9PositiveEigenIndices v).card = 8 := by
  have htotal := source9Eigenvalue_sign_partition_card v hv
  rw [source9SpinIndex_card_sixteen] at htotal
  have hequal := source9Eigenvalue_sign_card_equal v hv
  omega

/-- For each nonzero original nine-vector, EXACTLY eight source
spinor-index eigenvalues equal the negative real square-root. -/
theorem source9NegativeEigenIndices_card_eight
    (v : SpaceIndex → ℝ) (hv : v ≠ 0) :
    (source9NegativeEigenIndices v).card = 8 := by
  have htotal := source9Eigenvalue_sign_partition_card v hv
  rw [source9SpinIndex_card_sixteen] at htotal
  have hequal := source9Eigenvalue_sign_card_equal v hv
  omega

#print axioms source9SpinIndex_card_sixteen
#print axioms source9PositiveEigenIndices_card_eight
#print axioms source9NegativeEigenIndices_card_eight

end
end FCP.BFSSPairedSpin9DetFixture
