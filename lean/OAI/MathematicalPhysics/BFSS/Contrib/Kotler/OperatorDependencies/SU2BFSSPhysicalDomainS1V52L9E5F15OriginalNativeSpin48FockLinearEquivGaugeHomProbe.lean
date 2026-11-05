import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F14OriginalNativeSixteenSpin48FockRepresentationHomProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F11OriginalNativeSixteenSpin48FockTwoSidedUnitarityProbe

/-!
S1V52L9E5F15 — STAGED ONLY, NO STRICT CI UNTIL F14 ACCEPTED.

Bridge from the actual original SU2 → native sixteen-block Spin48
Fock continuous-linear operator monoid representation to a
genuine group representation by COMPLEX-LINEAR EQUIVALENCES on
the original original-source Fermion 2 Hilbert space.
Each inverse is the actual HILBERT adjoint established by F11,
not an unproved arbitrary inverse or projective scalar choice.

This typed group representation makes the qualified S1H unique
48-theta-covariant source-gauge hom theorem applicable after
an additional exact covariance bridge from F13's normalized
Gamma to the ORIGINAL unscaled pairedTheta. No physical gauge
equality, all Spin48-unitarity, or BFSS spectral claim here.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F15
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F11
open FCP.BFSSS1V52L9E5F14

private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

private abbrev originalNativeFockOp (g : GaugeGroup 2) : FockOp :=
  originalNativeSixteenSpinFockMonoidHom g

/-- EXACT original-source SU(2) native sixteen-block Spin48 Fock
Hilbert operator packaged as a bona fide COMPLEX-LINEAR
equivalence; the inverse is its accepted Hilbert adjoint. -/
noncomputable def originalNativeSixteenFockLinearEquiv
    (g : GaugeGroup 2) : Fermion 2 ≃ₗ[ℂ] Fermion 2 where
  toFun := originalNativeFockOp g
  invFun := (star (originalNativeFockOp g) : FockOp)
  left_inv := by
    intro v
    change (star (originalNativeFockOp g) * originalNativeFockOp g) v = v
    have h := originalNativeSixteenSpin48Fock_adjoint_mul g
    change star (originalNativeFockOp g) * originalNativeFockOp g =
      (1 : FockOp) at h
    rw [h]
    rfl
  right_inv := by
    intro v
    change (originalNativeFockOp g * star (originalNativeFockOp g)) v = v
    have h := originalNativeSixteenSpin48Fock_mul_adjoint g
    change originalNativeFockOp g * star (originalNativeFockOp g) =
      (1 : FockOp) at h
    rw [h]
    rfl
  map_add' := (originalNativeFockOp g).map_add
  map_smul' := (originalNativeFockOp g).map_smul

/-- The true original native sixteen-block Spin48 Fock operators
form a genuine complex-linear-equivalence representation, not
merely pointwise invertible operators. -/
noncomputable def originalNativeSixteenFockLinearEquivHom :
    GaugeGroup 2 →* (Fermion 2 ≃ₗ[ℂ] Fermion 2) where
  toFun := originalNativeSixteenFockLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change (originalNativeSixteenSpinFockMonoidHom (1 : GaugeGroup 2)) v = v
    rw [map_one originalNativeSixteenSpinFockMonoidHom]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change (originalNativeSixteenSpinFockMonoidHom (g * h)) v =
      (originalNativeSixteenSpinFockMonoidHom g)
        ((originalNativeSixteenSpinFockMonoidHom h) v)
    rw [map_mul originalNativeSixteenSpinFockMonoidHom]
    rfl

#print axioms originalNativeSixteenFockLinearEquiv
#print axioms originalNativeSixteenFockLinearEquivHom

end
end FCP.BFSSS1V52L9E5F15
