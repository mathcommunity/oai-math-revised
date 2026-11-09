import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9NativeSkewCommutatorClosureProbe

/-!
K1D18V9P — exact original paired-Fock typed skew carriers
and native matrix commutator preservation between those carriers.

V9C established skewness of the exact 48-real image; V9N
proved source-native skew commutator preservation; V9O
proved native 9×9 skew closure. This stage defines explicit
source 9-index and paired-Fock 48-real skew subtypes and
their actual matrix commutators without assuming a LieHom.

These are typed commutator carriers, not yet declared to be
Mathlib Lie algebras. A genuine LieHom, group integration and
BFSS physical/spectral existence are separate obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- Exact native 9×9 real skew carrier. -/
abbrev coordinateSkewMatrix9Carrier :=
  { A : Matrix SpaceIndex SpaceIndex ℝ // A.transpose = -A }

/-- Original paired-Fock 48-real skew carrier. -/
abbrev pairedSkewMatrix48Carrier :=
  { X : Matrix Source48Label Source48Label ℝ // X.transpose = -X }

/-- The accepted real coefficient map genuinely sends the native
skew carrier into original paired-Fock 48-real skew matrices. -/
noncomputable def coordinateToPairedSkewCarrier
    (A : coordinateSkewMatrix9Carrier) : pairedSkewMatrix48Carrier :=
  ⟨coordinateToPairedLinearMap A.val,
    coordinateToPairedLinearMap_image_transpose A.val⟩

/-- The source-native commutator is closed in the real 9×9 skew carrier. -/
noncomputable def coordinateSkewMatrix9Carrier_commutator
    (A B : coordinateSkewMatrix9Carrier) : coordinateSkewMatrix9Carrier :=
  ⟨A.val * B.val - B.val * A.val,
    coordinateSkewMatrix9_commutator_closed A.val B.val A.property B.property⟩

/-- The original paired-Fock real 48×48 skew carrier is closed
under the exact matrix product commutator. -/
theorem pairedSkewMatrix48_commutator_closed
    (X Y : Matrix Source48Label Source48Label ℝ)
    (hX : X.transpose = -X)
    (hY : Y.transpose = -Y) :
    (X * Y - Y * X).transpose = -(X * Y - Y * X) := by
  calc
    (X * Y - Y * X).transpose =
        Y.transpose * X.transpose - X.transpose * Y.transpose := by
      rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
    _ = -(X * Y - Y * X) := by
      rw [hX, hY]
      simp only [neg_mul, mul_neg, neg_neg, neg_sub]

/-- Actual original paired-Fock 48-real skew commutator carrier. -/
noncomputable def pairedSkewMatrix48Carrier_commutator
    (X Y : pairedSkewMatrix48Carrier) : pairedSkewMatrix48Carrier :=
  ⟨X.val * Y.val - Y.val * X.val,
    pairedSkewMatrix48_commutator_closed X.val Y.val X.property Y.property⟩

/-- Exact source-native skew-to-original-Fock-paired-skew map
preserves the actual typed matrix commutator in both carriers. -/
theorem coordinateToPairedSkewCarrier_commutator
    (A B : coordinateSkewMatrix9Carrier) :
    coordinateToPairedSkewCarrier (coordinateSkewMatrix9Carrier_commutator A B) =
      pairedSkewMatrix48Carrier_commutator
        (coordinateToPairedSkewCarrier A)
        (coordinateToPairedSkewCarrier B) := by
  apply Subtype.ext
  exact coordinateToPairedLinearMap_skew_commutator
    A.val B.val A.property B.property

#print axioms pairedSkewMatrix48_commutator_closed
#print axioms coordinateToPairedSkewCarrier_commutator

end
end FCP.BFSSPairedSpin9Plane
