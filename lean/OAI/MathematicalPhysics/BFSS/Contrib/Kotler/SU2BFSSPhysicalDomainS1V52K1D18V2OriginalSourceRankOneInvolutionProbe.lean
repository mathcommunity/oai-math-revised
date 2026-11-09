import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V1OriginalSourceRankOneReflectionGeometryProbe

/-!
K1D18V2 — true source rank-one Clifford reflection is pointwise
involutive on the original Fin 24 × Fin 2 vector representation.

First prove a generic source-sized matrix identity from the precise
row-dot-axis value 2; only then specialize to the accepted B polar
row and S1V0 source quadratic form. This keeps the source sign
2P_a-I explicit, with no surrogate basis.

No Q-isometry, original Clifford star/unitarity, Spin membership,
finite reflection generation, surjectivity, covering or BFSS spectrum
is asserted. CANDIDATE pending fresh strict CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V2
noncomputable section
open FCP.BFSSS1V0
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- A normalized rank-one line reflection is its own inverse,
pointwise on the original 48 coordinates. In particular this fixes
the sign convention independently of source specialization. -/
theorem source48_rankOneConjugationMatrix_square_mulVec
    (a ell v : Source48Vector)
    (hnormal : ell ⬝ᵥ a = (2 : ℝ)) :
    FCP.BFSSS1V37.source48_rankOneConjugationMatrix a ell *ᵥ
      (FCP.BFSSS1V37.source48_rankOneConjugationMatrix a ell *ᵥ v) = v := by
  have hrow :
      ell ⬝ᵥ ((ell ⬝ᵥ v) • a - v) = ell ⬝ᵥ v := by
    rw [dotProduct_sub, dotProduct_smul, hnormal]
    simp only [smul_eq_mul]
    ring
  rw [FCP.BFSSS1V52K1D18C.source48_rankOneConjugationMatrix_mulVec,
    FCP.BFSSS1V52K1D18C.source48_rankOneConjugationMatrix_mulVec,
    hrow]
  abel

/-- The actual original-source Clifford rank-one matrix, using the
accepted normalized Q-polar row, squares to the identity on every
source vector. Retains the exact invertible original source Q(a)
premise; constructs no normalized vector or Spin element. -/
theorem source48_originalCliffordRankOne_square_mulVec
    (a v : Source48Vector) [Invertible (Q a)] :
    FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
      (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) *ᵥ
    (FCP.BFSSS1V37.source48_rankOneConjugationMatrix a
      (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) *ᵥ v) = v := by
  exact source48_rankOneConjugationMatrix_square_mulVec
    a (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow a) v
    (FCP.BFSSS1V52K1D18B.source48NormalizedPolarRow_dot_self a)

#print axioms source48_rankOneConjugationMatrix_square_mulVec
#print axioms source48_originalCliffordRankOne_square_mulVec

end
end FCP.BFSSS1V52K1D18V2
