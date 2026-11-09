import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7DOriginalSourceSOWitnessEuclideanTransportProbe
import Mathlib.LinearAlgebra.Determinant

/-!
K1D18V7E — exact original source-SO to Euclidean determinant transport.

The original S1V0 48-coordinate source Q, the K1D18R actual
source-special-orthogonal witness group, accepted V7C canonical
same-label Euclidean linear equivalence, and accepted V7D source
Q-isometry witness are kept unchanged.

Pinned Mathlib's LinearEquiv.det_conj proves the general conjugacy
invariance at an ABSTRACT real-linear equivalence before ANY
source-specific specialization. The sourceSO determinant +1 is
already carried by the ORIGINAL K1D18R subgroup intersection.
The final theorem concerns the ACTUAL Euclidean LinearIsometryEquiv,
not a new source form.

No Cartan reflection factorization is translated into original
Clifford line-axis matrices here; the original sourceSO unit-pair
generation, Spin48 image surjectivity, covering, global Spin9, and
BFSS physical spectral claims remain separate unproved obligations.
CANDIDATE pending independent pinned strict verification.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7E
noncomputable section
open FCP.BFSSS1V0

private abbrev GL48 := Source48Vector ≃ₗ[ℝ] Source48Vector
private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL

/-- Generic, source-independent determinant conjugation bridge.
Pinned LinearEquiv.trans_assoc is definitional, so no 48-label
quadratic-form reduction or global proof-limit increase is needed. -/
theorem linearEquiv_conjugate_det_eq
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (f : V ≃ₗ[ℝ] V) (e : V ≃ₗ[ℝ] W) :
    LinearEquiv.det (e.symm.trans (f.trans e)) = LinearEquiv.det f := by
  exact LinearEquiv.det_conj f e

/-- The ACTUAL original K1D18R sourceSO subgroup already includes
the determinant-one kernel of the original GL48. -/
theorem originalSourceSO_det_one (g : SourceSO) :
    LinearEquiv.det (g : GL48) = 1 := by
  have h : (g : GL48) ∈ (LinearEquiv.det : GL48 →* ℝˣ).ker := g.property.2
  change LinearEquiv.det (g : GL48) = 1 at h
  exact h

/-- The exact same-label V7C conjugation preserves the determinant
of the ORIGINAL sourceSO underlying GL48 element, by V7D's
already-qualified exact witness equality. -/
theorem originalSourceSO_euclideanDet_eq_sourceDet (g : SourceSO) :
    LinearEquiv.det
      (FCP.BFSSS1V52K1D18V7C.originalSourceQIsometry_toEuclideanLinearEquiv
        (FCP.BFSSS1V52K1D18V7D.sourceSO_originalQIsometry g)) =
      LinearEquiv.det (g : GL48) := by
  let e := FCP.BFSSS1V52K1D18V7C.originalSource48ToEuclidean
  let f : GL48 := FCP.BFSSS1V52K1D18V7D.sourceSO_originalQIsometry g
  have hd : LinearEquiv.det (e.symm.trans (f.trans e)) = LinearEquiv.det f :=
    linearEquiv_conjugate_det_eq f e
  calc
    LinearEquiv.det
        (FCP.BFSSS1V52K1D18V7C.originalSourceQIsometry_toEuclideanLinearEquiv
          (FCP.BFSSS1V52K1D18V7D.sourceSO_originalQIsometry g)) =
        LinearEquiv.det (e.symm.trans (f.trans e)) := rfl
    _ = LinearEquiv.det f := hd
    _ = LinearEquiv.det (g : GL48) := by
      exact congrArg LinearEquiv.det
        (FCP.BFSSS1V52K1D18V7D.sourceSO_originalQIsometry_underlying g)

/-- Every ORIGINAL sourceSO element's transported genuine Euclidean
linear equivalence has determinant exactly +1. -/
theorem originalSourceSO_euclideanLinearEquiv_det_one (g : SourceSO) :
    LinearEquiv.det
      (FCP.BFSSS1V52K1D18V7C.originalSourceQIsometry_toEuclideanLinearEquiv
        (FCP.BFSSS1V52K1D18V7D.sourceSO_originalQIsometry g)) = 1 := by
  exact (originalSourceSO_euclideanDet_eq_sourceDet g).trans
    (originalSourceSO_det_one g)

/-- Determinant +1 for the ACTUAL Euclidean LinearIsometryEquiv
produced by accepted V7D, not merely for an auxiliary unrelated
linear equivalence. It says nothing about reflection generation. -/
theorem originalSourceSO_euclideanIsometry_det_one (g : SourceSO) :
    LinearEquiv.det
      (FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry g).toLinearEquiv = 1 := by
  change LinearEquiv.det
    (FCP.BFSSS1V52K1D18V7C.originalSourceQIsometry_toEuclideanLinearEquiv
      (FCP.BFSSS1V52K1D18V7D.sourceSO_originalQIsometry g)) = 1
  exact originalSourceSO_euclideanLinearEquiv_det_one g

#print axioms linearEquiv_conjugate_det_eq
#print axioms originalSourceSO_det_one
#print axioms originalSourceSO_euclideanDet_eq_sourceDet
#print axioms originalSourceSO_euclideanLinearEquiv_det_one
#print axioms originalSourceSO_euclideanIsometry_det_one

end
end FCP.BFSSS1V52K1D18V7E
