import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F13OriginalNativeSixteenSpin48UnitaryFockMajoranaCovarianceProbe

/-!
L9E5F14 — STAGED / UNQUALIFIED source-exact group-representation
interface, not the physical gauge-implementation equality.

The ACTUAL source SU(2) -> genuine Spin(48) native ordered
sixteen-block MonoidHom from L8E, composed with the ACTUAL original
CliffordAlgebra -> Fermion2 Hilbert continuous complex-linear
operator real algebra hom from C1, must be an exact MonoidHom into
the multiplicative monoid of original Fock operators.
No commutativity or abstract substitute action is used.

Accepted F11 supplies two-sided Hilbert-adjoint inverses for
each value; F13 separately proves the true generator covariance.
This root records the exact multiplicative interface needed
to invoke the already accepted source S1H relative-gauge
uniqueness theorem after an explicit continuous-linear-to-
linear-equivalence bridge and paired-theta normalization.
No equality to independently defined physical gauge action,
unitary character triviality, or BFSS spectrum is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F14
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F13

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- The ACTUAL original native sixteen-block source Spin48
SU2 representation as a multiplicative original Fock
continuous-linear-operator homomorphism. Not a surrogate
Hilbert module or a quotient projective representation. -/
noncomputable def originalNativeSixteenSpinFockMonoidHom :
    GaugeGroup 2 →* FockOp where
  toFun g :=
    originalFockCliffordAlgHom
      (((originalNativeSixteenSpinHom g : spinGroup Q) : C))
  map_one' := by
    change originalFockCliffordAlgHom
      (((originalNativeSixteenSpinHom (1 : GaugeGroup 2) :
        spinGroup Q) : C)) = (1 : FockOp)
    rw [map_one originalNativeSixteenSpinHom]
    change originalFockCliffordAlgHom (1 : C) = (1 : FockOp)
    exact map_one originalFockCliffordAlgHom
  map_mul' g h := by
    change originalFockCliffordAlgHom
      (((originalNativeSixteenSpinHom (g * h) : spinGroup Q) : C)) =
      originalFockCliffordAlgHom
        (((originalNativeSixteenSpinHom g : spinGroup Q) : C)) *
      originalFockCliffordAlgHom
        (((originalNativeSixteenSpinHom h : spinGroup Q) : C))
    calc
      originalFockCliffordAlgHom
          (((originalNativeSixteenSpinHom (g * h) : spinGroup Q) : C)) =
        originalFockCliffordAlgHom
          (((originalNativeSixteenSpinHom g *
            originalNativeSixteenSpinHom h : spinGroup Q) : C)) := by
              rw [map_mul]
      _ = originalFockCliffordAlgHom
            (((originalNativeSixteenSpinHom g : spinGroup Q) : C) *
              ((originalNativeSixteenSpinHom h : spinGroup Q) : C)) := by
                rfl
      _ = originalFockCliffordAlgHom
            (((originalNativeSixteenSpinHom g : spinGroup Q) : C)) *
          originalFockCliffordAlgHom
            (((originalNativeSixteenSpinHom h : spinGroup Q) : C)) := by
              rw [map_mul]

#print axioms originalNativeSixteenSpinFockMonoidHom

end
end FCP.BFSSS1V52L9E5F14
