import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9C3OriginalNativeColorAdjointMatrixBridgeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9B4OriginalSameBlockQuaternionConjugationProbe

/-!
S1V52L9D1 — STAGED, UNQUALIFIED exact ORIGINAL GaugeGroup2
same-block Spin(48) Clifford-Majorana conjugation equals original
paired BFSS color-adjoint coefficients on every source color axis.

This is deliberately downstream of the actual native L9C3
pairedAlgebraData.adjointCoefficient ↔ original quaternion rotation.
No substitute group, Pauli matrices, Clifford form or source label order.
L9C3 must qualify in its own strict gate before this source is tested.

Original sixteeen-block global projection predicate, actual Fock
implementation/continuity, physical Hamiltonian and spectral results
remain OPEN. Do not accept these statements before strict pinned CI.
-/

set_option autoImplicit false
set_option maxHeartbeats 430000

namespace FCP.BFSSS1V52L9D1
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52A
open FCP.BFSSS1V52B1
open FCP.BFSSS1V52C1
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L9B4
open FCP.BFSSS1V52L9C1
open FCP.BFSSS1V52L9C3
open FCP.BFSSSU2GaugeG3A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev E (α : RealSpinBlock) (i : Fin 3) : C :=
  CliffordAlgebra.ι Q (sourceBlockColorAxis α i)

/-- The first exact original SOURCE48 Majorana color axis transforms
with the actual pinned BFSS native SU2 adjoint-color column 0. -/
theorem originalNativeSameBlockSpinClifford_axis0
    (α : RealSpinBlock) (g : GaugeGroup 2) :
    ((originalNativeGaugeSpinHom α g : spinGroup Q) : C) *
      E α 0 * star ((originalNativeGaugeSpinHom α g : spinGroup Q) : C) =
      (adjointColorMatrix g (0 : Fin 3) (0 : Fin 3)) • E α 0 +
      (adjointColorMatrix g (1 : Fin 3) (0 : Fin 3)) • E α 1 +
      (adjointColorMatrix g (2 : Fin 3) (0 : Fin 3)) • E α 2 := by
  simp only [originalNativeGaugeSpinHom_coe,
    originalNativeAdjointColorMatrix_eq_quaternion]
  simpa [originalQuaternionAdjointPolynomial] using
    (originalSameBlockQuaternion_conj_axis0 α
      (originalNativeQuaternionCoords g))

/-- Second exact source Majorana color axis: original column 1. -/
theorem originalNativeSameBlockSpinClifford_axis1
    (α : RealSpinBlock) (g : GaugeGroup 2) :
    ((originalNativeGaugeSpinHom α g : spinGroup Q) : C) *
      E α 1 * star ((originalNativeGaugeSpinHom α g : spinGroup Q) : C) =
      (adjointColorMatrix g (0 : Fin 3) (1 : Fin 3)) • E α 0 +
      (adjointColorMatrix g (1 : Fin 3) (1 : Fin 3)) • E α 1 +
      (adjointColorMatrix g (2 : Fin 3) (1 : Fin 3)) • E α 2 := by
  simp only [originalNativeGaugeSpinHom_coe,
    originalNativeAdjointColorMatrix_eq_quaternion]
  simpa [originalQuaternionAdjointPolynomial] using
    (originalSameBlockQuaternion_conj_axis1 α
      (originalNativeQuaternionCoords g))

/-- Third exact source Majorana color axis: original column 2. -/
theorem originalNativeSameBlockSpinClifford_axis2
    (α : RealSpinBlock) (g : GaugeGroup 2) :
    ((originalNativeGaugeSpinHom α g : spinGroup Q) : C) *
      E α 2 * star ((originalNativeGaugeSpinHom α g : spinGroup Q) : C) =
      (adjointColorMatrix g (0 : Fin 3) (2 : Fin 3)) • E α 0 +
      (adjointColorMatrix g (1 : Fin 3) (2 : Fin 3)) • E α 1 +
      (adjointColorMatrix g (2 : Fin 3) (2 : Fin 3)) • E α 2 := by
  simp only [originalNativeGaugeSpinHom_coe,
    originalNativeAdjointColorMatrix_eq_quaternion]
  simpa [originalQuaternionAdjointPolynomial] using
    (originalSameBlockQuaternion_conj_axis2 α
      (originalNativeQuaternionCoords g))

#print axioms originalNativeSameBlockSpinClifford_axis0
#print axioms originalNativeSameBlockSpinClifford_axis1
#print axioms originalNativeSameBlockSpinClifford_axis2

end
end FCP.BFSSS1V52L9D1
