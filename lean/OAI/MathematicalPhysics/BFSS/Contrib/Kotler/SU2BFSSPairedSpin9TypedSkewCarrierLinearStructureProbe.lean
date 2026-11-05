import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9TypedSkewCarrierCommutatorProbe

/-!
K1D18V9Q — native and original paired-Fock skew carrier additive
and real scalar closure, plus exact carrier map additivity and
real homogeneity.

The skew carriers and actual matrix commutators were qualified
by V9P. This small stage adds *explicitly typed* addition and
scalar multiplication interfaces without assuming a LieHom
or claiming built-in Module instances for the subtypes.

All operations use source SpaceIndex and original paired
Source48Label ordering. Global Spin(9) integration and BFSS
physical/spectral claims are separate unproved obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- Exact source native 9×9 skew addition. -/
noncomputable def coordinateSkewMatrix9Carrier_add
    (A B : coordinateSkewMatrix9Carrier) : coordinateSkewMatrix9Carrier :=
  ⟨A.val + B.val, by
    rw [Matrix.transpose_add, A.property, B.property, neg_add]⟩

/-- Exact original paired-Fock 48×48 skew addition. -/
noncomputable def pairedSkewMatrix48Carrier_add
    (X Y : pairedSkewMatrix48Carrier) : pairedSkewMatrix48Carrier :=
  ⟨X.val + Y.val, by
    rw [Matrix.transpose_add, X.property, Y.property, neg_add]⟩

/-- Exact source-native 9×9 skew real scalar multiplication. -/
noncomputable def coordinateSkewMatrix9Carrier_smul
    (c : ℝ) (A : coordinateSkewMatrix9Carrier) :
    coordinateSkewMatrix9Carrier :=
  ⟨c • A.val, by
    rw [Matrix.transpose_smul, A.property, smul_neg]⟩

/-- Exact original paired-Fock 48×48 skew real scalar multiplication. -/
noncomputable def pairedSkewMatrix48Carrier_smul
    (c : ℝ) (X : pairedSkewMatrix48Carrier) :
    pairedSkewMatrix48Carrier :=
  ⟨c • X.val, by
    rw [Matrix.transpose_smul, X.property, smul_neg]⟩

/-- Source-exact coefficient map respects typed skew addition. -/
theorem coordinateToPairedSkewCarrier_add
    (A B : coordinateSkewMatrix9Carrier) :
    coordinateToPairedSkewCarrier (coordinateSkewMatrix9Carrier_add A B) =
      pairedSkewMatrix48Carrier_add
        (coordinateToPairedSkewCarrier A)
        (coordinateToPairedSkewCarrier B) := by
  apply Subtype.ext
  change coordinateToPairedLinearMap (A.val + B.val) =
    coordinateToPairedLinearMap A.val + coordinateToPairedLinearMap B.val
  exact map_add coordinateToPairedLinearMap A.val B.val

/-- Source-exact coefficient map respects typed real skew scalars. -/
theorem coordinateToPairedSkewCarrier_smul
    (c : ℝ) (A : coordinateSkewMatrix9Carrier) :
    coordinateToPairedSkewCarrier (coordinateSkewMatrix9Carrier_smul c A) =
      pairedSkewMatrix48Carrier_smul c (coordinateToPairedSkewCarrier A) := by
  apply Subtype.ext
  change coordinateToPairedLinearMap (c • A.val) =
    c • coordinateToPairedLinearMap A.val
  exact map_smul coordinateToPairedLinearMap c A.val

#print axioms coordinateToPairedSkewCarrier_add
#print axioms coordinateToPairedSkewCarrier_smul

end
end FCP.BFSSPairedSpin9Plane
