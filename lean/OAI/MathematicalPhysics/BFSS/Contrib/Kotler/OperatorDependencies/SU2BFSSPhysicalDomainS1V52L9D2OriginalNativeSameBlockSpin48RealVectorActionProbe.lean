import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9D1OriginalNativeSameBlockSpinCliffordAdjointProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V31CanonicalAllSpin48RealVectorActionProbe

/-!
S1V52L9D2 — STAGED, UNQUALIFIED: genuine original Spin(48) REAL
48-dimensional source-vector action on an individual native SU2 block,
expressed through the actual original BFSS adjointColorMatrix.

This is the real-vector extraction step after strict L9D1 source
Clifford conjugation. No independent orthogonal representation or
unproved injectivity axiom is introduced: source S1V30 proves Clifford
generator injectivity, and source S1V31 proves Spin-unit conjugation
maps each original real generator into an original real generator.

DO NOT launch CI before L9D1 is kernel-qualified. All 16 factors,
original full Fock matrix action, global sourceSpin48CoversActualGauge,
continuity, Hamiltonian domains, and spectral statements remain OPEN.
-/

set_option autoImplicit false
set_option maxHeartbeats 380000

namespace FCP.BFSSS1V52L9D2
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L9D1
open FCP.BFSSSU2GaugeG3A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Exact source real-vector extraction from original Clifford
conjugation, using accepted injectivity of the source Clifford
generator and S1V31's genuine Spin(48) action. -/
private theorem sourceSpin48VectorAction_eq_of_clifford
    (s : spinGroup Q) (v w : Source48Vector)
    (h : (s : C) * CliffordAlgebra.ι Q v * star (s : C) =
      CliffordAlgebra.ι Q w) :
    FCP.BFSSS1V31.sourceSpin48VectorAction s v = w := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q
        (FCP.BFSSS1V31.sourceSpin48VectorAction s v) =
      ConjAct.toConjAct (spinGroup.toUnits s) • CliffordAlgebra.ι Q v :=
        FCP.BFSSS1V31.sourceSpin48VectorAction_clifford_generator s v
    _ = (s : C) * CliffordAlgebra.ι Q v * star (s : C) := by rfl
    _ = CliffordAlgebra.ι Q w := h

/-- Original BFSS native gauge color adjoint rotates the source real
48-dimensional Majorana axis 0 inside its unchanged spin block. -/
theorem originalNativeSameBlockSpin48Vector_axis0
    (α : RealSpinBlock) (g : GaugeGroup 2) :
    FCP.BFSSS1V31.sourceSpin48VectorAction
      (originalNativeGaugeSpinHom α g) (sourceBlockColorAxis α 0) =
      (adjointColorMatrix g (0 : Fin 3) (0 : Fin 3)) •
          sourceBlockColorAxis α 0 +
      (adjointColorMatrix g (1 : Fin 3) (0 : Fin 3)) •
          sourceBlockColorAxis α 1 +
      (adjointColorMatrix g (2 : Fin 3) (0 : Fin 3)) •
          sourceBlockColorAxis α 2 := by
  apply sourceSpin48VectorAction_eq_of_clifford
  simpa only [map_add, map_smul] using
    (originalNativeSameBlockSpinClifford_axis0 α g)

/-- Same actual source real 48-vector action on color axis 1. -/
theorem originalNativeSameBlockSpin48Vector_axis1
    (α : RealSpinBlock) (g : GaugeGroup 2) :
    FCP.BFSSS1V31.sourceSpin48VectorAction
      (originalNativeGaugeSpinHom α g) (sourceBlockColorAxis α 1) =
      (adjointColorMatrix g (0 : Fin 3) (1 : Fin 3)) •
          sourceBlockColorAxis α 0 +
      (adjointColorMatrix g (1 : Fin 3) (1 : Fin 3)) •
          sourceBlockColorAxis α 1 +
      (adjointColorMatrix g (2 : Fin 3) (1 : Fin 3)) •
          sourceBlockColorAxis α 2 := by
  apply sourceSpin48VectorAction_eq_of_clifford
  simpa only [map_add, map_smul] using
    (originalNativeSameBlockSpinClifford_axis1 α g)

/-- Same actual source real 48-vector action on color axis 2. -/
theorem originalNativeSameBlockSpin48Vector_axis2
    (α : RealSpinBlock) (g : GaugeGroup 2) :
    FCP.BFSSS1V31.sourceSpin48VectorAction
      (originalNativeGaugeSpinHom α g) (sourceBlockColorAxis α 2) =
      (adjointColorMatrix g (0 : Fin 3) (2 : Fin 3)) •
          sourceBlockColorAxis α 0 +
      (adjointColorMatrix g (1 : Fin 3) (2 : Fin 3)) •
          sourceBlockColorAxis α 1 +
      (adjointColorMatrix g (2 : Fin 3) (2 : Fin 3)) •
          sourceBlockColorAxis α 2 := by
  apply sourceSpin48VectorAction_eq_of_clifford
  simpa only [map_add, map_smul] using
    (originalNativeSameBlockSpinClifford_axis2 α g)

#print axioms originalNativeSameBlockSpin48Vector_axis0
#print axioms originalNativeSameBlockSpin48Vector_axis1
#print axioms originalNativeSameBlockSpin48Vector_axis2

end
end FCP.BFSSS1V52L9D2
