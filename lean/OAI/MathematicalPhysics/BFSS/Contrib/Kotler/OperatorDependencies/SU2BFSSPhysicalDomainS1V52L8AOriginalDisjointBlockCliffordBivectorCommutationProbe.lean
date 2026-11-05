import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L7C7OriginalNativeEulerWitnessAndSpinHomProbe

/-!
S1V52-L8A — STAGED, UNQUALIFIED original-source disjoint-block
Clifford bivector commutation.

The pinned source geometric support is the actual original
48-real Fin24 × Fin2 Majorana label space and its quadratic form,
with `RealSpinBlock` from the original 16×3 source color geometry.

Reuses accepted S1V6 `sourceBlockColorAxis_ortho` for ANY distinct
spin blocks, and the same two-sign-change noncommutative Clifford
argument as strictly accepted S1V4.

Do not generalize S1V8's single fixed rotor to arbitrary native SU2
images without proving these generic source cross-color relations.
No commutative Clifford algebra assumption, hidden orthogonality
axiom, surrogate spin group, or change in original +i signs.

All declarations remain unqualified until source-pinned strict CI
validates their Lean kernel proofs and axiom reports.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52L8A
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V6
open FCP.BFSSS1V52A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q
private abbrev E (α : RealSpinBlock) (i : Fin 3) : C :=
  CliffordAlgebra.ι Q (sourceBlockColorAxis α i)

/-- Any original-source color generator in block α commutes with
ANY even pair of original source color generators in disjoint block β.
The reason is exactly two anticommutations, no commutative-C premise. -/
theorem originalDisjointBlockAxis_comm_bivector
    (α β : RealSpinBlock) (hab : α ≠ β)
    (i j k : Fin 3) :
    E α i * (E β j * E β k) =
      (E β j * E β k) * E α i := by
  have hcross (r : Fin 3) :
      Q.IsOrtho (sourceBlockColorAxis α i)
        (sourceBlockColorAxis β r) := by
    apply sourceBlockColorAxis_ortho (α, i) (β, r)
    intro h
    exact hab (congrArg Prod.fst h)
  have hij : E α i * E β j = -(E β j * E α i) := by
    exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (hcross j)
  have hik : E α i * E β k = -(E β k * E α i) := by
    exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (hcross k)
  calc
    E α i * (E β j * E β k) =
        (E α i * E β j) * E β k := by simp only [mul_assoc]
    _ = (-(E β j * E α i)) * E β k := by rw [hij]
    _ = -(E β j * (E α i * E β k)) := by
      simp only [neg_mul, mul_assoc]
    _ = -(E β j * (-(E β k * E α i))) := by rw [hik]
    _ = E β j * (E β k * E α i) := by
      simp only [mul_neg, neg_neg]
    _ = (E β j * E β k) * E α i := by simp only [mul_assoc]

/-- Every original-source Clifford even bivector supported on spin
block α commutes with every bivector supported on different β.
All four cross-block orthogonality facts are proved via S1V6. -/
theorem originalDisjointBlockBivectors_comm
    (α β : RealSpinBlock) (hab : α ≠ β)
    (i j k l : Fin 3) :
    (E α i * E α j) * (E β k * E β l) =
      (E β k * E β l) * (E α i * E α j) := by
  have hi :
      E α i * (E β k * E β l) =
        (E β k * E β l) * E α i :=
    originalDisjointBlockAxis_comm_bivector α β hab i k l
  have hj :
      E α j * (E β k * E β l) =
        (E β k * E β l) * E α j :=
    originalDisjointBlockAxis_comm_bivector α β hab j k l
  calc
    (E α i * E α j) * (E β k * E β l) =
        E α i * (E α j * (E β k * E β l)) := by
          simp only [mul_assoc]
    _ = E α i * ((E β k * E β l) * E α j) := by rw [hj]
    _ = (E α i * (E β k * E β l)) * E α j := by
      simp only [mul_assoc]
    _ = ((E β k * E β l) * E α i) * E α j := by rw [hi]
    _ = (E β k * E β l) * (E α i * E α j) := by
      simp only [mul_assoc]

#print axioms originalDisjointBlockAxis_comm_bivector
#print axioms originalDisjointBlockBivectors_comm

end
end FCP.BFSSS1V52L8A
