import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10ZSourceNineExteriorPBWOrderedWordProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9V10HF10EPublicGammaTraceZeroProbe

/-!
K1D18V10H-F10AA — first ACTUAL even gamma-matrix word
separation, not just a new Clifford PBW interface.

For distinct original source SpaceIndex labels a,b, the
original real sixteen-dimensional gamma matrices satisfy:
* trace(gamma a * gamma b) = 0;
* gamma a * gamma b is nonzero;
* gamma a * gamma b is NOT a scalar matrix.

Use the already accepted original PUBLIC Clifford relations
from F10E, not private signed-permutation tables, replaced
gamma matrices, 48-label surrogates or Fock assumptions.

This only separates a single length-two even gamma word
from the scalar subspace. All 256 even PBW gamma images are
NOT yet proved linearly independent; a full faithful Spin9
representation, Spin48 lift and BFSS physics remain open.

CANDIDATE until fresh pinned strict compiler and three
independently elaborated axiom/type audits pass.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Clifford
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSGamma9
open FCP.BFSSPairedSpin9DetFixture
open Matrix

/-- For two DISTINCT original nine-source labels, the true
original sixteen-real gamma-pair matrix has zero trace.
Only the public Clifford anticommutator and cyclic trace
are used. -/
theorem source9OriginalGamma_pair_trace_zero
    (a b : SpaceIndex) (hab : a ≠ b) :
    Matrix.trace (gamma a * gamma b) = 0 := by
  have hswap :
      gamma b * gamma a = -(gamma a * gamma b) :=
    source9OriginalGamma_anticommute b a hab.symm
  have htr :
      Matrix.trace (gamma a * gamma b) =
        -Matrix.trace (gamma a * gamma b) := by
    calc
      Matrix.trace (gamma a * gamma b) =
          Matrix.trace (gamma b * gamma a) :=
        Matrix.trace_mul_comm _ _
      _ = -Matrix.trace (gamma a * gamma b) := by
        rw [hswap, Matrix.trace_neg]
  linarith

/-- Original gamma-pair word cannot vanish: each original
gamma is an involution, and multiplying the purported
zero gamma-pair by gamma b would force gamma a = 0,
contradicting its square identity at (0,0). -/
theorem source9OriginalGamma_pair_ne_zero
    (a b : SpaceIndex) :
    gamma a * gamma b ≠ (0 : GammaMatrix) := by
  intro hz
  have ha : gamma a = (0 : GammaMatrix) := by
    calc
      gamma a = gamma a * (1 : GammaMatrix) :=
        (mul_one _).symm
      _ = gamma a * (gamma b * gamma b) := by
        rw [source9OriginalGamma_basis_mul_self b]
      _ = (gamma a * gamma b) * gamma b := by
        rw [mul_assoc]
      _ = 0 := by rw [hz, zero_mul]
  have hsq := source9OriginalGamma_basis_mul_self a
  rw [ha] at hsq
  have hdiag := congrArg
    (fun M : GammaMatrix => M (0 : SpinIndex) (0 : SpinIndex)) hsq
  norm_num at hdiag

/-- The actual original length-two even gamma word for
distinct source directions is NON-SCALAR (not any real
multiple of the sixteen-real identity matrix). This is
the first bounded coefficient-separation result beyond
the source Clifford/exterior PBW basis. -/
theorem source9OriginalGamma_pair_not_scalar
    (a b : SpaceIndex) (hab : a ≠ b) (r : ℝ) :
    gamma a * gamma b ≠ r • (1 : GammaMatrix) := by
  intro hscalar
  have htrace := congrArg Matrix.trace hscalar
  have htr1 : Matrix.trace (1 : GammaMatrix) = (16 : ℝ) := by
    norm_num [Matrix.trace_one]
  rw [source9OriginalGamma_pair_trace_zero a b hab,
    Matrix.trace_smul, htr1] at htrace
  have hr : r = 0 := by
    simp only [smul_eq_mul] at htrace
    linarith
  have hzero : gamma a * gamma b = (0 : GammaMatrix) := by
    simpa [hr] using hscalar
  exact source9OriginalGamma_pair_ne_zero a b hzero

#print axioms source9OriginalGamma_pair_trace_zero
#print axioms source9OriginalGamma_pair_ne_zero
#print axioms source9OriginalGamma_pair_not_scalar

end
end FCP.BFSSPairedSpin9Clifford
