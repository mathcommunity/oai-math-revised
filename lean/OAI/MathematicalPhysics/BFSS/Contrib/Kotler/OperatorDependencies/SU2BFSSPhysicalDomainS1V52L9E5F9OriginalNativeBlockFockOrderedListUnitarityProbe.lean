import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F8OriginalNativeSpin48BlockFockUnitaryProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L8EOriginalOrderedSixteenNativeSU2Spin48HomProbe

/-!
S1V52L9E5F9 — STAGED / UNQUALIFIED, NO CI.

An intermediate noncommutative product theorem for the genuine
original Fermion-2 Hilbert operators, using one actual original
native Spin48 block per member of an arbitrary finite ordered
list. It is deliberately NOT yet the equality between the
Fock image of `originalNativeSixteenSpinHom g` and this list
product. That source-to-operator product bridge is a separate
obligation, as is the physical gauge implementer comparison.

Assumes predecessor F8 original native single-block unitary
roots only after strict acceptance. No commutative Spin target,
no surrogate Fock space, no BFSS spectrum or mass-gap claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F9
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5F8

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

private abbrev nativeBlockFockOp (α : RealSpinBlock)
    (g : GaugeGroup 2) : FockOp :=
  originalFockCliffordAlgHom
    (((originalNativeGaugeSpinHom α g : spinGroup Q) : C))

/-- The actual source order; never commutate operators. -/
private def nativeBlockFockOrderedProd
    (xs : List RealSpinBlock) (g : GaugeGroup 2) : FockOp :=
  (xs.map (fun α => nativeBlockFockOp α g)).prod

private theorem nativeBlockFockOrderedProd_nil (g : GaugeGroup 2) :
    nativeBlockFockOrderedProd [] g = (1 : FockOp) := by
  simp only [nativeBlockFockOrderedProd, List.map_nil, List.prod_nil]

private theorem nativeBlockFockOrderedProd_cons
    (α : RealSpinBlock) (xs : List RealSpinBlock)
    (g : GaugeGroup 2) :
    nativeBlockFockOrderedProd (α :: xs) g =
      nativeBlockFockOp α g * nativeBlockFockOrderedProd xs g := by
  simp only [nativeBlockFockOrderedProd, List.map_cons, List.prod_cons]

private theorem actualFock_star_one :
    star (1 : FockOp) = (1 : FockOp) := by
  simp only [star_one]

private theorem actualFock_unitary_mul_left (A B : FockOp)
    (ha : star A * A = 1) (hb : star B * B = 1) :
    star (A * B) * (A * B) = 1 := by
  calc
    star (A * B) * (A * B) =
        (star B * star A) * (A * B) := by rw [star_mul]
    _ = star B * ((star A * A) * B) := by simp only [mul_assoc]
    _ = star B * B := by rw [ha]; simp only [one_mul]
    _ = 1 := hb

private theorem actualFock_unitary_mul_right (A B : FockOp)
    (ha : A * star A = 1) (hb : B * star B = 1) :
    (A * B) * star (A * B) = 1 := by
  calc
    (A * B) * star (A * B) =
        (A * B) * (star B * star A) := by rw [star_mul]
    _ = A * ((B * star B) * star A) := by simp only [mul_assoc]
    _ = A * star A := by rw [hb]; simp only [one_mul]
    _ = 1 := ha

/-- The actual original native Spin48 block Fock images have
left Hilbert-adjoint inverse when multiplied in ANY specified
finite list order. -/
theorem originalNativeBlockFockOrderedProd_adjoint_mul
    (g : GaugeGroup 2) (xs : List RealSpinBlock) :
    star (nativeBlockFockOrderedProd xs g) *
      nativeBlockFockOrderedProd xs g = (1 : FockOp) := by
  induction xs with
  | nil =>
      rw [nativeBlockFockOrderedProd_nil]
      rw [actualFock_star_one]
      simp only [one_mul]
  | cons α xs ih =>
      rw [nativeBlockFockOrderedProd_cons]
      exact actualFock_unitary_mul_left
        (nativeBlockFockOp α g)
        (nativeBlockFockOrderedProd xs g)
        (originalNativeBlockSpin48Fock_adjoint_mul α g)
        ih

/-- Right Hilbert-adjoint inverse for the same genuine
ordered product, with NO commutative factor reordering. -/
theorem originalNativeBlockFockOrderedProd_mul_adjoint
    (g : GaugeGroup 2) (xs : List RealSpinBlock) :
    nativeBlockFockOrderedProd xs g *
      star (nativeBlockFockOrderedProd xs g) = (1 : FockOp) := by
  induction xs with
  | nil =>
      rw [nativeBlockFockOrderedProd_nil]
      rw [actualFock_star_one]
      simp only [mul_one]
  | cons α xs ih =>
      rw [nativeBlockFockOrderedProd_cons]
      exact actualFock_unitary_mul_right
        (nativeBlockFockOp α g)
        (nativeBlockFockOrderedProd xs g)
        (originalNativeBlockSpin48Fock_mul_adjoint α g)
        ih

#print axioms originalNativeBlockFockOrderedProd_adjoint_mul
#print axioms originalNativeBlockFockOrderedProd_mul_adjoint

end
end FCP.BFSSS1V52L9E5F9
