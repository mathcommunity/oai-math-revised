import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8OOriginalSU2SourceInfinitesimalColorSpanProbe
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
L6H5E8P — exact ORIGINAL GaugeGroup 2 matrix quaternion form.

This is the next necessary finite-dimensional step toward
an explicit source normalized-Pauli SU2 Euler decomposition:
every original determinant-one unitary 2x2 gauge matrix
has the quaternionic form [u,v;-conj(v),conj(u)].

Derive the claim ONLY from pinned Matrix.specialUnitaryGroup
membership, adjugate_fin_two and matrix unitarity:
det=1 and g†*g=1 force adjugate(g)=g†.

Does not assume SU2 connectedness, exp surjectivity,
Pauli color-curve generation or BFSS spectral claims.
Original source +i convention and gauge action untouched.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8P
noncomputable section
open OAI.BFSSQuantum
open Matrix

/-- For every EXACT original SU2 gauge matrix, the
matrix adjugate equals its Hermitian adjoint. -/
theorem originalSU2_adjugate_eq_conjTranspose
    (g : GaugeGroup 2) :
    Matrix.adjugate (g : ColorMatrix 2) =
      (g : ColorMatrix 2)ᴴ := by
  let A : ColorMatrix 2 := g
  have hd : Matrix.det A = 1 := g.property.2
  have hu : Aᴴ * A = (1 : ColorMatrix 2) := by
    have hm : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := g.property.1
    simpa only [Matrix.star_eq_conjTranspose] using hm.1
  have ha : A * Matrix.adjugate A = (1 : ColorMatrix 2) := by
    simpa only [hd, one_smul] using Matrix.mul_adjugate A
  change Matrix.adjugate A = Aᴴ
  calc
    Matrix.adjugate A = 1 * Matrix.adjugate A :=
      (one_mul _).symm
    _ = (Aᴴ * A) * Matrix.adjugate A := by rw [hu]
    _ = Aᴴ * (A * Matrix.adjugate A) := by rw [mul_assoc]
    _ = Aᴴ := by rw [ha, mul_one]

/-- Original SU2 matrix lower-right entry is precisely
the complex conjugate of its upper-left entry. -/
theorem originalSU2_bottomRight_eq_conj_topLeft
    (g : GaugeGroup 2) :
    ((g : ColorMatrix 2) 1 1) =
      star ((g : ColorMatrix 2) 0 0) := by
  have he := congrArg
    (fun A : ColorMatrix 2 => A 0 0)
    (originalSU2_adjugate_eq_conjTranspose g)
  -- #338: '!![...; ...]' expands to Matrix.of vecCons, so
  -- simpa only [cons_val_*] leaves literal matrix applications.
  -- The pinned matrix-notation simp rules reduce fixed Fin 2 entries.
  simpa [Matrix.adjugate_fin_two] using he

/-- Original SU2 matrix lower-left entry is negative
the complex conjugate of its upper-right entry. -/
theorem originalSU2_bottomLeft_eq_neg_conj_topRight
    (g : GaugeGroup 2) :
    ((g : ColorMatrix 2) 1 0) =
      -star ((g : ColorMatrix 2) 0 1) := by
  have he := congrArg
    (fun A : ColorMatrix 2 => A 1 0)
    (originalSU2_adjugate_eq_conjTranspose g)
  have hneg :
      -((g : ColorMatrix 2) 1 0) =
        star ((g : ColorMatrix 2) 0 1) := by
    -- Same #338 missing Matrix.of/vecCons simp reductions.
    simpa [Matrix.adjugate_fin_two] using he
  calc
    ((g : ColorMatrix 2) 1 0) =
        -(-((g : ColorMatrix 2) 1 0)) := by simp
    _ = -star ((g : ColorMatrix 2) 0 1) := by rw [hneg]

#print axioms originalSU2_adjugate_eq_conjTranspose
#print axioms originalSU2_bottomRight_eq_conj_topLeft
#print axioms originalSU2_bottomLeft_eq_neg_conj_topRight
#check @originalSU2_bottomRight_eq_conj_topLeft
#check @originalSU2_bottomLeft_eq_neg_conj_topRight

end
end FCP.BFSSSU2PhysicalDomainL6H5E8P
