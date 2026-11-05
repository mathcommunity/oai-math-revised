import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5WOriginalOrbitalGaugeTangentProbe

/-!
L6G6A — original fermionic coefficient-response, evaluated on the ACTUAL
source SmoothCore. The G4B commutator response is a position multiplier;
this stage identifies its literal scalar coefficient at every x.

This is an exact source operator-to-pointwise bridge for arbitrary N and
arbitrary real w. It does not yet apply the original G2 row Fierz identity,
reorder Majorana operators, or assert the fermionic Gauss/Hamiltonian
identity. No new physical or spectral conclusion is claimed.
-/

set_option autoImplicit false

namespace FCP.BFSSSU2PhysicalDomainL6G6A
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G4B

/-- The explicit original derivative-of-quadratic-position coefficient. -/
def sourcePositionPairPoint {N : ℕ}
    (u v t : BosonLabel N) (x : Boson N) : ℂ :=
  (if u = v then ((x t : ℝ) : ℂ) else 0) +
  (if u = t then ((x v : ℝ) : ℂ) else 0)

/-- L6G4A's ORIGINAL operator-valued derivative response evaluated on the
original smooth core, with both Kronecker contractions retained. -/
theorem sourcePositionPairResponse_apply {N : ℕ}
    (u v t : BosonLabel N) (f : SmoothCore N) (x : Boson N) :
    ((sourcePositionPairResponse u v t) f) x =
      (sourcePositionPairPoint u v t x) • f x := by
  classical
  -- A conditional SourceEnd cannot be evaluated by definitional equality.
  -- Discharge evaluation before summing the two Kronecker terms.
  have hite (P : Prop) [Decidable P] (a : BosonLabel N) :
      (((if P then sourceP a else 0) f) x) =
        (if P then ((x a : ℝ) : ℂ) else 0) • f x := by
    by_cases hp : P
    · simp only [_root_.ite_eq_left hp]
      rfl
    · simp only [_root_.ite_eq_right hp, LinearMap.zero_apply, zero_smul, zero_apply]
  calc
    ((sourcePositionPairResponse u v t) f) x =
        (((if u = v then sourceP t else 0) f) x) +
        (((if u = t then sourceP v else 0) f) x) := rfl
    _ = (if u = v then ((x t : ℝ) : ℂ) else 0) • f x +
        (if u = t then ((x v : ℝ) : ℂ) else 0) • f x := by
          rw [hite (u = v) t, hite (u = t) v]
    _ = (sourcePositionPairPoint u v t x) • f x := by
          unfold sourcePositionPairPoint
          rw [add_smul]

/-- Every coefficient here is pulled from G4B's actual source kinetic and
quadratic terms, with the original -i and 1/2 normalization unchanged. -/
def sourceCoefficientResponsePoint {N : ℕ}
    (M : AlgebraData N) (α β : SpinIndex)
    (p q : FermionLabel N) (x : Boson N) : ℂ :=
  ∑ u : BosonLabel N, ∑ v : BosonLabel N, ∑ t : BosonLabel N,
    (sourceKineticWeight M α p u * sourceQuadraticWeight M β q v t -
      sourceKineticWeight M β q u * sourceQuadraticWeight M α p v t) *
        sourcePositionPairPoint u v t x

/-- Evaluation is linear in the genuine original core endomorphism. -/
private def evalSourceResponse {N : ℕ}
    (f : SmoothCore N) (x : Boson N) :
    SourceEnd N →ₗ[ℂ] Fermion N where
  toFun A := (A f) x
  map_add' A B := by rfl
  map_smul' c A := by rfl

/-- The literal original G4B coefficient commutator is pointwise
multiplication by a linear polynomial in the original bosonic coordinates. -/
theorem sourceCoefficientResponse_apply {N : ℕ}
    (M : AlgebraData N) (α β : SpinIndex)
    (p q : FermionLabel N) (f : SmoothCore N) (x : Boson N) :
    ((sourceCoefficientResponse M α β p q) f) x =
      (sourceCoefficientResponsePoint M α β p q x) • f x := by
  classical
  calc
    _ = ∑ u : BosonLabel N, ∑ v : BosonLabel N, ∑ t : BosonLabel N,
      (sourceKineticWeight M α p u * sourceQuadraticWeight M β q v t -
        sourceKineticWeight M β q u * sourceQuadraticWeight M α p v t) •
          (((sourcePositionPairResponse u v t) f) x) := by
            change (evalSourceResponse f x)
              (sourceCoefficientResponse M α β p q) = _
            unfold sourceCoefficientResponse
            simp only [map_sum, map_smul]
            rfl
    _ = ∑ u : BosonLabel N, ∑ v : BosonLabel N, ∑ t : BosonLabel N,
      ((sourceKineticWeight M α p u * sourceQuadraticWeight M β q v t -
        sourceKineticWeight M β q u * sourceQuadraticWeight M α p v t) *
          sourcePositionPairPoint u v t x) • f x := by
            simp_rw [sourcePositionPairResponse_apply, smul_smul]
    _ = _ := by
      unfold sourceCoefficientResponsePoint
      simp only [Finset.sum_smul]

/-- Source all-spinor response coefficient, with ALL alpha/beta weights.
The Fierz and color contractions are deliberately left to L6G6B. -/
def sourceAllSpinorResponsePoint {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (p q : FermionLabel N) (x : Boson N) : ℂ :=
  ∑ α : SpinIndex, ∑ β : SpinIndex,
    ((w α : ℂ) * (w β : ℂ)) *
      sourceCoefficientResponsePoint M α β p q x

/-- The complete coefficient commutator is a true source scalar multiplier
BEFORE multiplying by the ordered original Majorana pair. -/
theorem sourceAllSpinorCoefficientResponse_apply {N : ℕ}
    (M : AlgebraData N) (w : SpinIndex → ℝ)
    (p q : FermionLabel N) (f : SmoothCore N) (x : Boson N) :
    ((sourceAllSpinorCoefficientResponse M w p q) f) x =
      (sourceAllSpinorResponsePoint M w p q x) • f x := by
  classical
  calc
    _ = ∑ α : SpinIndex, ∑ β : SpinIndex,
      ((w α : ℂ) * (w β : ℂ)) •
        (((sourceCoefficientResponse M α β p q) f) x) := by
          change (evalSourceResponse f x)
            (sourceAllSpinorCoefficientResponse M w p q) = _
          unfold sourceAllSpinorCoefficientResponse
          simp only [map_sum, map_smul]
          rfl
    _ = ∑ α : SpinIndex, ∑ β : SpinIndex,
      (((w α : ℂ) * (w β : ℂ)) *
        sourceCoefficientResponsePoint M α β p q x) • f x := by
          simp_rw [sourceCoefficientResponse_apply, smul_smul]
    _ = _ := by
      unfold sourceAllSpinorResponsePoint
      simp only [Finset.sum_smul]

#print axioms sourcePositionPairResponse_apply
#print axioms sourceCoefficientResponse_apply
#print axioms sourceAllSpinorCoefficientResponse_apply
#check @sourceAllSpinorCoefficientResponse_apply
end
end FCP.BFSSSU2PhysicalDomainL6G6A
