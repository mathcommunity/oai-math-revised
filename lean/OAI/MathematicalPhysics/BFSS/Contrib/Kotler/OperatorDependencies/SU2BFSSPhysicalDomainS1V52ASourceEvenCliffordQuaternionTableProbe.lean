import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V6ConcreteSource48ColorAxisOrthogonalityProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
S1V52-A — CANDIDATE original 48-real source three-color even-Clifford
quaternion table, using the EXACT S1V0/S1V5/S1V6 source Q and actual
Fin24 × Fin2 paired Majorana geometry. No alternative Clifford model.

The basis is oriented to the ACTUAL positive-i original Pauli matrices:
  Z = ι(e₀)ι(e₁),  Y = ι(e₂)ι(e₀),  X = ι(e₁)ι(e₂).
Then Z*Y=X, Y*X=Z, X*Z=Y, and each square is -1.
At the accepted historical z-quarter the expected polynomial is
Z, not -Z: S1V49 independently constructs precisely the same
16-block Z product. This file does NOT prove polynomial multiplicativity
for all gauge elements, Spin membership, cross-block commutation,
source projection, continuity, nor any physical/spectral result.

RESEARCH CANDIDATE: no theorem in this file is accepted until an
independent PINNED STRICT CI proof/axiom audit compiles all exact roots.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52A
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V6

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Exact original Majorana Clifford generator on one of 16 source
spin blocks, not a surrogate 3-real Clifford algebra. -/
private abbrev E (α : RealSpinBlock) (A : Fin 3) : C :=
  CliffordAlgebra.ι Q (sourceBlockColorAxis α A)

theorem sourceAxis_square (α : RealSpinBlock) (A : Fin 3) :
    E α A * E α A = 1 := by
  change CliffordAlgebra.ι Q (sourceBlockColorAxis α A) *
      CliffordAlgebra.ι Q (sourceBlockColorAxis α A) = 1
  rw [CliffordAlgebra.ι_sq_scalar,
    sourceBlockColorAxis_unit α A, map_one]

theorem sourceAxis_anticomm (α : RealSpinBlock) (A B : Fin 3)
    (hAB : A ≠ B) :
    E α A * E α B = -(E α B * E α A) := by
  have hpair : (α, A) ≠ (α, B) := by
    intro h
    exact hAB (congrArg Prod.snd h)
  exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
    (sourceBlockColorAxis_ortho (α,A) (α,B) hpair)

/-- For ANY noncommutative ring (here the actual source Clifford
algebra), the three elementary sign and norm relations suffice for
the positively oriented bivector cycle. There is no CommMagma C. -/
private theorem triple_bivector_cycle
    (A B D : C)
    (hAA : A * A = 1)
    (hBA : B * A = -(A * B))
    (hDA : D * A = -(A * D)) :
    (A * B) * (D * A) = B * D := by
  calc
    (A * B) * (D * A) = A * (B * (D * A)) := by
      simp only [mul_assoc]
    _ = A * (B * (-(A * D))) := by rw [hDA]
    _ = -(A * ((B * A) * D)) := by
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = -(A * ((-(A * B)) * D)) := by rw [hBA]
    _ = (A * A) * (B * D) := by
      simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
    _ = B * D := by rw [hAA, one_mul]

/-- Reverse cyclic products have the opposite sign; this explicitly
uses the genuine anticommuting source generators. -/
private theorem triple_bivector_reverse
    (A B D : C)
    (hAA : A * A = 1)
    (hDB : D * B = -(B * D)) :
    (D * A) * (A * B) = -(B * D) := by
  calc
    (D * A) * (A * B) = D * ((A * A) * B) := by
      simp only [mul_assoc]
    _ = D * B := by rw [hAA, one_mul]
    _ = -(B * D) := hDB

private theorem orthogonal_pair_square
    (A B : C)
    (hAA : A * A = 1) (hBB : B * B = 1)
    (hBA : B * A = -(A * B)) :
    (A * B) * (A * B) = -1 := by
  calc
    (A * B) * (A * B) = A * (B * A) * B := by
      simp only [mul_assoc]
    _ = A * (-(A * B)) * B := by rw [hBA]
    _ = -((A * A) * (B * B)) := by
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = -1 := by rw [hAA, hBB, one_mul]

/-- Positive-i z: the historical quarter source rotor's LOCAL factor. -/
noncomputable def sourceZBivector (α : RealSpinBlock) : C :=
  E α 0 * E α 1

/-- Positive-i y: the source quaternion's real off-diagonal direction. -/
noncomputable def sourceYBivector (α : RealSpinBlock) : C :=
  E α 2 * E α 0

/-- Positive-i x: the source quaternion's imaginary off-diagonal direction. -/
noncomputable def sourceXBivector (α : RealSpinBlock) : C :=
  E α 1 * E α 2

theorem sourceZBivector_square (α : RealSpinBlock) :
    sourceZBivector α * sourceZBivector α = -1 := by
  change (E α 0 * E α 1) * (E α 0 * E α 1) = -1
  exact orthogonal_pair_square _ _
    (sourceAxis_square α 0) (sourceAxis_square α 1)
    (sourceAxis_anticomm α 1 0 (by decide))

theorem sourceYBivector_square (α : RealSpinBlock) :
    sourceYBivector α * sourceYBivector α = -1 := by
  change (E α 2 * E α 0) * (E α 2 * E α 0) = -1
  exact orthogonal_pair_square _ _
    (sourceAxis_square α 2) (sourceAxis_square α 0)
    (sourceAxis_anticomm α 0 2 (by decide))

theorem sourceXBivector_square (α : RealSpinBlock) :
    sourceXBivector α * sourceXBivector α = -1 := by
  change (E α 1 * E α 2) * (E α 1 * E α 2) = -1
  exact orthogonal_pair_square _ _
    (sourceAxis_square α 1) (sourceAxis_square α 2)
    (sourceAxis_anticomm α 2 1 (by decide))

theorem sourceZ_mul_Y (α : RealSpinBlock) :
    sourceZBivector α * sourceYBivector α =
      sourceXBivector α := by
  change (E α 0 * E α 1) * (E α 2 * E α 0) = E α 1 * E α 2
  exact triple_bivector_cycle _ _ _
    (sourceAxis_square α 0)
    (sourceAxis_anticomm α 1 0 (by decide))
    (sourceAxis_anticomm α 2 0 (by decide))

theorem sourceY_mul_X (α : RealSpinBlock) :
    sourceYBivector α * sourceXBivector α =
      sourceZBivector α := by
  change (E α 2 * E α 0) * (E α 1 * E α 2) = E α 0 * E α 1
  exact triple_bivector_cycle _ _ _
    (sourceAxis_square α 2)
    (sourceAxis_anticomm α 0 2 (by decide))
    (sourceAxis_anticomm α 1 2 (by decide))

theorem sourceX_mul_Z (α : RealSpinBlock) :
    sourceXBivector α * sourceZBivector α =
      sourceYBivector α := by
  change (E α 1 * E α 2) * (E α 0 * E α 1) = E α 2 * E α 0
  exact triple_bivector_cycle _ _ _
    (sourceAxis_square α 1)
    (sourceAxis_anticomm α 2 1 (by decide))
    (sourceAxis_anticomm α 0 1 (by decide))

theorem sourceY_mul_Z (α : RealSpinBlock) :
    sourceYBivector α * sourceZBivector α =
      -sourceXBivector α := by
  change (E α 2 * E α 0) * (E α 0 * E α 1) = -(E α 1 * E α 2)
  exact triple_bivector_reverse _ _ _
    (sourceAxis_square α 0)
    (sourceAxis_anticomm α 2 1 (by decide))

theorem sourceX_mul_Y (α : RealSpinBlock) :
    sourceXBivector α * sourceYBivector α =
      -sourceZBivector α := by
  change (E α 1 * E α 2) * (E α 2 * E α 0) = -(E α 0 * E α 1)
  exact triple_bivector_reverse _ _ _
    (sourceAxis_square α 2)
    (sourceAxis_anticomm α 1 0 (by decide))

theorem sourceZ_mul_X (α : RealSpinBlock) :
    sourceZBivector α * sourceXBivector α =
      -sourceYBivector α := by
  change (E α 0 * E α 1) * (E α 1 * E α 2) = -(E α 2 * E α 0)
  exact triple_bivector_reverse _ _ _
    (sourceAxis_square α 1)
    (sourceAxis_anticomm α 0 2 (by decide))

#print axioms sourceAxis_square
#print axioms sourceAxis_anticomm
#print axioms sourceZBivector_square
#print axioms sourceYBivector_square
#print axioms sourceXBivector_square
#print axioms sourceZ_mul_Y
#print axioms sourceY_mul_X
#print axioms sourceX_mul_Z
#print axioms sourceY_mul_Z
#print axioms sourceX_mul_Y
#print axioms sourceZ_mul_X

end
end FCP.BFSSS1V52A
