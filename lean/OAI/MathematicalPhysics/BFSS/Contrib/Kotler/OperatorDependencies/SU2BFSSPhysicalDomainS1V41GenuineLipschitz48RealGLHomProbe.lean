import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V40ActualSource48LipschitzVectorActionProbe
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
S1V41 — original source-sized genuine Lipschitz group composition,
real-linear automorphism, and real determinant character.

Every object is derived from S1V40's actual
  x : lipschitzGroup source48Quadratic
Clifford conjugation action on Fin 24 × Fin 2 → ℝ.
The multiplication convention is the correct Clifford composition,
not reversed isometry-equivalence trans composition.

NO determinant sign/parity, Spin orientation, Spin covering, global SU2
lift, manuscript representation or BFSS spectral theorem is claimed.
The seven roots are unqualified until an exact-source strict gate.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V41
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V40

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Actual original Lipschitz unit identity has trivial Clifford-conjugation action. -/
theorem sourceLipschitz48VectorAction_one (v : Source48Vector) :
    sourceLipschitz48VectorAction (1 : lipschitzGroup Q) v = v := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q (sourceLipschitz48VectorAction (1 : lipschitzGroup Q) v) =
        ConjAct.toConjAct ((1 : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) •
          (CliffordAlgebra.ι Q v) :=
      sourceLipschitz48VectorAction_clifford (1 : lipschitzGroup Q) v
    _ = CliffordAlgebra.ι Q v := by simp

/-- The action respects multiplication in the actual Mathlib subgroup
of Clifford units. The action of x*y is action x after action y. -/
theorem sourceLipschitz48VectorAction_mul
    (x y : lipschitzGroup Q) (v : Source48Vector) :
    sourceLipschitz48VectorAction (x * y) v =
      sourceLipschitz48VectorAction x
        (sourceLipschitz48VectorAction y v) := by
  apply FCP.BFSSS1V30.source48_cliffordGenerator_injective
  calc
    CliffordAlgebra.ι Q (sourceLipschitz48VectorAction (x * y) v) =
        ConjAct.toConjAct ((x * y : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) •
          (CliffordAlgebra.ι Q v) :=
      sourceLipschitz48VectorAction_clifford (x * y) v
    _ =
        ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ) •
          (ConjAct.toConjAct (y : (CliffordAlgebra Q)ˣ) •
            (CliffordAlgebra.ι Q v)) := by
      change ConjAct.toConjAct
        ((x : (CliffordAlgebra Q)ˣ) * (y : (CliffordAlgebra Q)ˣ)) •
        (CliffordAlgebra.ι Q v) =
        ConjAct.toConjAct (x : (CliffordAlgebra Q)ˣ) •
          (ConjAct.toConjAct (y : (CliffordAlgebra Q)ˣ) •
            (CliffordAlgebra.ι Q v))
      rw [ConjAct.toConjAct_mul, mul_smul]
    _ =
        CliffordAlgebra.ι Q
          (sourceLipschitz48VectorAction x
            (sourceLipschitz48VectorAction y v)) := by
      rw [sourceLipschitz48VectorAction_clifford,
        sourceLipschitz48VectorAction_clifford]

/-- The original real-linear Lipschitz action is invertible: its inverse
is the action of the genuine inverse Clifford unit. -/
noncomputable def sourceLipschitz48LinearEquiv (x : lipschitzGroup Q) :
    Source48Vector ≃ₗ[ℝ] Source48Vector where
  toFun := sourceLipschitz48VectorAction x
  invFun := sourceLipschitz48VectorAction x⁻¹
  left_inv := by
    intro v
    change sourceLipschitz48VectorAction x⁻¹
      (sourceLipschitz48VectorAction x v) = v
    rw [← sourceLipschitz48VectorAction_mul,
      inv_mul_cancel, sourceLipschitz48VectorAction_one]
  right_inv := by
    intro v
    change sourceLipschitz48VectorAction x
      (sourceLipschitz48VectorAction x⁻¹ v) = v
    rw [← sourceLipschitz48VectorAction_mul,
      mul_inv_cancel, sourceLipschitz48VectorAction_one]
  map_add' := FCP.BFSSS1V40.sourceLipschitz48VectorAction_add x
  map_smul' := FCP.BFSSS1V40.sourceLipschitz48VectorAction_smul x

/-- The genuine identity unit acts as the identity real automorphism. -/
theorem sourceLipschitz48LinearEquiv_one :
    sourceLipschitz48LinearEquiv (1 : lipschitzGroup Q) =
      (1 : Source48Vector ≃ₗ[ℝ] Source48Vector) := by
  apply LinearEquiv.ext
  intro v
  change sourceLipschitz48VectorAction (1 : lipschitzGroup Q) v = v
  exact sourceLipschitz48VectorAction_one v

/-- Multiplication of actual Lipschitz units yields the correct
automorphism-group multiplication, not reverse trans order. -/
theorem sourceLipschitz48LinearEquiv_mul (x y : lipschitzGroup Q) :
    sourceLipschitz48LinearEquiv (x * y) =
      sourceLipschitz48LinearEquiv x *
        sourceLipschitz48LinearEquiv y := by
  apply LinearEquiv.ext
  intro v
  change sourceLipschitz48VectorAction (x * y) v =
    sourceLipschitz48VectorAction x (sourceLipschitz48VectorAction y v)
  exact sourceLipschitz48VectorAction_mul x y v

/-- Source-genuine Lipschitz subgroup representation in original GL48,
with no unproved Pin/even-word decomposition. -/
noncomputable def sourceLipschitz48LinearEquivHom :
    lipschitzGroup Q →* (Source48Vector ≃ₗ[ℝ] Source48Vector) where
  toFun := sourceLipschitz48LinearEquiv
  map_one' := sourceLipschitz48LinearEquiv_one
  map_mul' := sourceLipschitz48LinearEquiv_mul

/-- Actual determinant character on the same genuine Lipschitz group;
this DOES NOT assert that its values equal any parity function yet. -/
noncomputable def sourceLipschitz48OriginalRealDetCharacter :
    lipschitzGroup Q →* ℝˣ :=
  (LinearEquiv.det :
    (Source48Vector ≃ₗ[ℝ] Source48Vector) →* ℝˣ).comp
      sourceLipschitz48LinearEquivHom

#print axioms sourceLipschitz48VectorAction_one
#print axioms sourceLipschitz48VectorAction_mul
#print axioms sourceLipschitz48LinearEquiv
#print axioms sourceLipschitz48LinearEquiv_one
#print axioms sourceLipschitz48LinearEquiv_mul
#print axioms sourceLipschitz48LinearEquivHom
#print axioms sourceLipschitz48OriginalRealDetCharacter

end
end FCP.BFSSS1V41
