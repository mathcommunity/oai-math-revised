import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2RealGammaProbe
import OAI.MathematicalPhysics.BFSS.GammaIdentity

/-!
# L6-G1 — exact pinned source spinor identity by upstream theorem reuse

GammaIdentity.lean proves the BFSS spinor identity for ANY nine real
symmetric gamma matrices satisfying the Euclidean Clifford relations.
This module instantiates that proof at the original FCP.BFSSGamma9.gamma,
used definitionally by concreteAlgebraData and pairedAlgebraData.

The upstream expression is in COLUMN-spinor gammaTwo orientation.
The earlier row-spinor Fierz contraction has the opposite sign due
to gammaTwo transpose = -gammaTwo; do not conflate orientations.

No axiom, sorry, native_decide, Fock source expansion, or spectral claim.
This source module is UNCOMPILED until pinned CI qualifies it.
-/
namespace FCP.BFSSSU2PhysicalDomainL6G1
noncomputable section
open scoped Matrix BigOperators
open Matrix
open OAI.BFSSGamma

abbrev originalGamma : OAI.BFSSGamma.Space → OAI.BFSSGamma.Mat :=
  FCP.BFSSGamma9.gamma

/-- The full, upstream kernel-derived BFSS spinor identity for the
ORIGINAL source-real Clifford construction, not an independent system. -/
theorem originalGamma_spinIdentity :
    OAI.BFSSGamma.SpinIdentity originalGamma := by
  exact OAI.BFSSGamma.spinIdentity originalGamma
    (fun i j => FCP.BFSSGamma9.gamma_clifford i j)
    (fun i => FCP.BFSSGamma9.gamma_symmetric i)

/-- The literal spinor coefficient identity, with the upstream
column-spinor convention and source-defined gammaTwo. -/
theorem originalGamma_spinIdentity_apply
    (v : OAI.BFSSGamma.Spin → ℝ)
    (hv : ∑ α : OAI.BFSSGamma.Spin, v α ^ 2 = 1)
    (j : OAI.BFSSGamma.Space) :
    (∑ i : OAI.BFSSGamma.Space,
      OAI.BFSSGamma.symm
        (Matrix.vecMulVec
          (originalGamma i *ᵥ v)
          (OAI.BFSSGamma.gammaTwo originalGamma i j *ᵥ v))) =
      ((1 / 2 : ℝ) * dotProduct v (originalGamma j *ᵥ v)) •
          (1 : OAI.BFSSGamma.Mat) -
        (1 / 2 : ℝ) • originalGamma j := by
  exact originalGamma_spinIdentity v hv j

#print axioms originalGamma_spinIdentity
#print axioms originalGamma_spinIdentity_apply

end
end FCP.BFSSSU2PhysicalDomainL6G1
