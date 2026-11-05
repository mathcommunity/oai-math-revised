import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7XOriginalSourceSOEuclideanDetOnePreimageProbe
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.LinearAlgebra.Determinant

/-!
K1D18V7Y — source-exact ALGEBRAIC identification of the
ACTUAL original sourceSO group with the entire native same-48-label
Euclidean determinant-one LinearIsometryEquiv subgroup.

Accepted V7E: the original genuine sourceSO Euclidean transport
has determinant +1. Accepted V7R: this SAME original transport
group hom is injective. Accepted V7X: EVERY genuine native
determinant-one Euclidean linear isometry has an original
sourceSO preimage, constructed from genuine source Clifford Spin.

New bounded obligations:
(1) package the native Euclidean LinearIsometryEquiv determinant
as an actual MonoidHom to real units;
(2) define the determinant-one subgroup as its ACTUAL kernel,
independently of the original source Spin/Clifford definition;
(3) prove the IMAGE of the original sourceSO Euclidean hom
equals precisely that NATIVE determinant-one subgroup;
(4) use pinned Mathlib MonoidHom.ofInjective plus subgroupCongr
to construct a genuine MulEquiv to that NATIVE determinant-one
subgroup, with exact original pointwise action.

NO claim of a topological Lie-group isomorphism, continuous
original Spin48-to-SO48 map, local covering, quotient topology,
global Spin9 lift or physical BFSS spectral theorem.
Every declaration CANDIDATE until strict source-pinned CI.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7Y
noncomputable section
open FCP.BFSSS1V0

private abbrev SourceSO :=
  FCP.BFSSS1V52K1D18R.source48SpecialOrthogonalWitnessGL
private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev EuclideanOrthogonal := Euc48 ≃ₗᵢ[ℝ] Euc48
private abbrev transport : SourceSO →* EuclideanOrthogonal :=
  FCP.BFSSS1V52K1D18V7P.originalSourceSO_toEuclideanHom

/-- Genuine same-48-label native Euclidean isometry
determinant, as a multiplicative group homomorphism. -/
noncomputable def nativeEuclideanDeterminantHom :
    EuclideanOrthogonal →* ℝˣ where
  toFun φ := LinearEquiv.det φ.toLinearEquiv
  map_one' := by
    change LinearEquiv.det (1 : Euc48 ≃ₗ[ℝ] Euc48) = 1
    exact map_one LinearEquiv.det
  map_mul' φ ψ := by
    change LinearEquiv.det (φ.toLinearEquiv * ψ.toLinearEquiv) =
      LinearEquiv.det φ.toLinearEquiv * LinearEquiv.det ψ.toLinearEquiv
    exact map_mul LinearEquiv.det φ.toLinearEquiv ψ.toLinearEquiv

/-- INDEPENDENT native Euclidean special-orthogonal subgroup:
the kernel of the ACTUAL native Euclidean determinant. -/
noncomputable def nativeEuclideanDetOneSubgroup :
    Subgroup EuclideanOrthogonal :=
  nativeEuclideanDeterminantHom.ker

/-- The original sourceSO Euclidean transport image is
PRECISELY the true native Euclidean determinant-one subgroup,
as subsets/subgroups of the same unchanged Euclidean group.
Forward uses V7E and reverse uses V7X. -/
theorem originalSourceSO_transport_range_eq_nativeEuclideanDetOne :
    transport.range = nativeEuclideanDetOneSubgroup := by
  ext φ
  constructor
  · rintro ⟨g, rfl⟩
    change LinearEquiv.det
      (FCP.BFSSS1V52K1D18V7D.sourceSO_toEuclideanIsometry g).toLinearEquiv = 1
    exact FCP.BFSSS1V52K1D18V7E.originalSourceSO_euclideanIsometry_det_one g
  · intro hφ
    have hdet : LinearEquiv.det φ.toLinearEquiv = 1 := by
      change LinearEquiv.det φ.toLinearEquiv = 1 at hφ
      exact hφ
    obtain ⟨g, hg⟩ :=
      FCP.BFSSS1V52K1D18V7X.euclideanDetOne_hasOriginalSourceSOPreimage φ hdet
    exact ⟨g, hg⟩

/-- ACTUAL algebraic group equivalence from the genuine
original sourceSO onto the INDEPENDENT same-48-label Euclidean
determinant-one subgroup. No coordinate permutation or
separate invented source SO action occurs. -/
noncomputable def originalSourceSO_toNativeEuclideanDetOneMulEquiv :
    SourceSO ≃* nativeEuclideanDetOneSubgroup :=
  (MonoidHom.ofInjective
    FCP.BFSSS1V52K1D18V7R.originalSourceSO_toEuclideanHom_injective).trans
      (MulEquiv.subgroupCongr
        originalSourceSO_transport_range_eq_nativeEuclideanDetOne)

/-- This group equivalence on each ACTUAL original sourceSO
element has exactly the already accepted same-label Euclidean
action of the ORIGINAL sourceSO transport. -/
theorem originalSourceSO_toNativeEuclideanDetOneMulEquiv_apply
    (g : SourceSO) :
    ((originalSourceSO_toNativeEuclideanDetOneMulEquiv g :
      nativeEuclideanDetOneSubgroup) : EuclideanOrthogonal) =
        transport g := by
  rfl

#print axioms nativeEuclideanDeterminantHom
#print axioms nativeEuclideanDetOneSubgroup
#print axioms originalSourceSO_transport_range_eq_nativeEuclideanDetOne
#print axioms originalSourceSO_toNativeEuclideanDetOneMulEquiv
#print axioms originalSourceSO_toNativeEuclideanDetOneMulEquiv_apply

end
end FCP.BFSSS1V52K1D18V7Y
