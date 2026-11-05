import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52ASourceEvenCliffordQuaternionTableProbe
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
S1V52-B1 — finite original +i normalized-Pauli SU2 quaternion COORDINATE
matrix multiplication. This tests the SAME 2x2 quaternion entry shape
as accepted L6H5E8Q, but has no new assumption about source gauge
elements. The previously qualified S1V52A genuine 48-source Clifford
algebra is imported to fix the original basis/orientation for B2.

These are real coordinate algebra identities on the exact 2x2 color
matrix size. The follow-up original GaugeGroup 2 bridge to L6H5E8Q,
the 48-source Clifford polynomial multiplicativity, and actual Spin
membership are expressly separate obligations.

Research candidate: no theorem accepted before strict pinned CI and
#print axioms. No replacement SU2 group, no negative-i convention.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52B1
noncomputable section

/-- Ordered original-source quaternion real coefficients:
top-left u=a+ib and top-right v=c+id. -/
structure SourceQuaternionCoords where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

/-- Quaternion product dictated by the positive-i Pauli identity
(Z,Y,X) and the accepted source Clifford table ZY=X, YX=Z, XZ=Y. -/
def sourceQuaternionCompose
    (p q : SourceQuaternionCoords) : SourceQuaternionCoords where
  a := p.a*q.a - p.b*q.b - p.c*q.c - p.d*q.d
  b := p.a*q.b + p.b*q.a + p.c*q.d - p.d*q.c
  c := p.a*q.c + p.c*q.a + p.d*q.b - p.b*q.d
  d := p.a*q.d + p.d*q.a + p.b*q.c - p.c*q.b

/-- Identity quaternion coefficients. -/
def sourceQuaternionOne : SourceQuaternionCoords :=
  ⟨1, 0, 0, 0⟩

/-- Exact literal standard-color SU2 matrix shape, with the
source-normalized +i Pauli x,y,z ordering and first row u,v.
This is NOT an alternate definition of native GaugeGroup 2. -/
def sourceQuaternionColorMatrix
    (p : SourceQuaternionCoords) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![
    (p.a : ℂ) + (p.b : ℂ)*Complex.I,
    (p.c : ℂ) + (p.d : ℂ)*Complex.I;
    -(p.c : ℂ) + (p.d : ℂ)*Complex.I,
    (p.a : ℂ) - (p.b : ℂ)*Complex.I
  ]

/-- The literal 2x2 color matrix for the quaternion identity equals
the original size-2 matrix identity. -/
theorem sourceQuaternionColorMatrix_one :
    sourceQuaternionColorMatrix sourceQuaternionOne =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceQuaternionColorMatrix, sourceQuaternionOne]

/-- Matrix multiplication exactly respects the positive-i real
quaternion coefficients. Unlike the full global Spin lift, this
identity is just a finite, original-sized complex matrix calculation. -/
theorem sourceQuaternionColorMatrix_compose
    (p q : SourceQuaternionCoords) :
    sourceQuaternionColorMatrix (sourceQuaternionCompose p q) =
      sourceQuaternionColorMatrix p * sourceQuaternionColorMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceQuaternionColorMatrix, sourceQuaternionCompose,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    simp [Complex.I_sq] <;>
    ring

/-- The +i matrix upper-left scalar component is exactly a+ib. -/
theorem sourceQuaternionColorMatrix_u
    (p : SourceQuaternionCoords) :
    sourceQuaternionColorMatrix p 0 0 =
      (p.a : ℂ) + (p.b : ℂ)*Complex.I := by
  simp [sourceQuaternionColorMatrix]

/-- The +i matrix upper-right scalar component is exactly c+id. -/
theorem sourceQuaternionColorMatrix_v
    (p : SourceQuaternionCoords) :
    sourceQuaternionColorMatrix p 0 1 =
      (p.c : ℂ) + (p.d : ℂ)*Complex.I := by
  simp [sourceQuaternionColorMatrix]

#print axioms sourceQuaternionColorMatrix_one
#print axioms sourceQuaternionColorMatrix_compose
#print axioms sourceQuaternionColorMatrix_u
#print axioms sourceQuaternionColorMatrix_v

end
end FCP.BFSSS1V52B1
