import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9D9OriginalNativeSixteenSpin48ActualGaugeUniversalProjectionProbe

/-!
S1V52L9E1 — STAGED, UNQUALIFIED exact universal source
Clifford-generator conjugation by the now qualified native
sixteen-block SU(2) → Spin(48) homomorphism.

The genuine Mathlib Clifford algebra, original quadratic form,
actual original BFSS sourceRealMajoranaMatrix on Source48Vector,
and original source L9D9 universal 48-real projection are used.
This theorem is about conjugation in the GENUINE abstract
Clifford algebra; it does not produce or assume any unitary
implementation on the original Fermion 2 Fock Hilbert space.

Source S1V31 already identifies the Clifford generator image of
the real Spin(48) action. The new theorem substitutes the *actual
original native Fock Majorana matrix* projection from accepted
L9D9. It is an interface for future independently qualified
Clifford-module/Fock operator transport.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000

namespace FCP.BFSSS1V52L9E1
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9D9
open FCP.BFSSSU2PhysicalDomainS1J

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Exact original SU2 sixteenth-block native Spin48 Clifford
conjugation on ANY original real 48-Majorana source vector:
the RHS is the pinned Fock source 48-real gauge matrix action,
not an auxiliary SO48 vector representation. -/
theorem originalNativeSixteenSpinHom_clifford_generator_conj
    (g : GaugeGroup 2) (v : Source48Vector) :
    ((originalNativeSixteenSpinHom g : spinGroup Q) : C) *
        CliffordAlgebra.ι Q v *
      star ((originalNativeSixteenSpinHom g : spinGroup Q) : C) =
        CliffordAlgebra.ι Q
          ((sourceRealMajoranaMatrix g).mulVec v) := by
  have hcl :=
    FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator
      (originalNativeSixteenSpinHom g) v
  change CliffordAlgebra.ι Q
      (FCP.BFSSS1V31.sourceSpin48VectorAction
        (originalNativeSixteenSpinHom g) v) =
      ((originalNativeSixteenSpinHom g : spinGroup Q) : C) *
        CliffordAlgebra.ι Q v *
      star ((originalNativeSixteenSpinHom g : spinGroup Q) : C)
    at hcl
  exact hcl.symm.trans
    (congrArg (CliffordAlgebra.ι Q)
      (originalNativeSixteenSpinHom_coversActualGauge g v))

#print axioms originalNativeSixteenSpinHom_clifford_generator_conj

end
end FCP.BFSSS1V52L9E1
