import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7LOriginalSourceSOEvenCartanListProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18V7COriginalSourceQuadraticIsometryEuclideanTransportProbe

/-!
K1D18V7M — inverse transport of TRUE same-48-label Euclidean
unit normals to genuine original source-Q unit vectors.

V7L is now accepted: each original sourceSO element admits an
even-length, ordered native Euclidean unit-normal Cartan list.
V7C is accepted: the exact coordinate-preserving original
Source48Vector-to-EuclideanSpace linear equivalence E satisfies
‖E a‖² = original source48Quadratic a for every ORIGINAL a.

This bounded candidate takes E.symm u, proves its original Q is
one for any norm-one Euclidean u, and proves exact forward
roundtrip. It extends the two properties pointwise to List.map.
No surrogate quadratic form, original source relabeling,
substitute Clifford representation or hidden generator axioms.

This is NOT an original Spin unit-pair generation theorem,
SO image-surjectivity theorem, covering, Spin9 lift, or BFSS
physical spectral assertion. Five roots CANDIDATE pending
strict warning-as-error compilation and independent axiom audit.
-/

set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18V7M
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev Euc48 := EuclideanSpace ℝ Source48Label
private abbrev E : Source48Vector ≃ₗ[ℝ] Euc48 :=
  FCP.BFSSS1V52K1D18V7C.originalSource48ToEuclidean

/-- The ACTUAL inverse coordinate identification (no permutation)
of a native Euclidean Cartan normal with the original 48 labels. -/
noncomputable def originalSourceUnitNormal (u : Euc48) : Source48Vector :=
  E.symm u

/-- Exact same-label roundtrip, used to compare native Euclidean
factor axes with original source rank-one Clifford axes. -/
theorem originalSourceUnitNormal_roundtrip (u : Euc48) :
    E (originalSourceUnitNormal u) = u := by
  change E (E.symm u) = u
  exact E.apply_symm_apply u

/-- Unit norm of the native Euclidean vector forces value 1 of
the ACTUAL original source quadratic form on its inverse image. -/
theorem originalSourceUnitNormal_Q_one (u : Euc48) (hu : ‖u‖ = 1) :
    Q (originalSourceUnitNormal u) = 1 := by
  have hsq :=
    FCP.BFSSS1V52K1D18V7C.originalSource48ToEuclidean_norm_sq_eq_Q
      (originalSourceUnitNormal u)
  calc
    Q (originalSourceUnitNormal u) =
        ‖E (originalSourceUnitNormal u)‖ ^ 2 := hsq.symm
    _ = ‖u‖ ^ 2 := by rw [originalSourceUnitNormal_roundtrip]
    _ = 1 := by rw [hu]; norm_num

/-- Every member of the ordered pulled-back list has genuinely
original source Q value 1, without a choice of substitute form. -/
theorem originalSourceUnitNormalList_all_Q_one (l : List Euc48)
    (hall : ∀ u ∈ l, ‖u‖ = 1) :
    ∀ v ∈ l.map originalSourceUnitNormal, Q v = 1 := by
  intro v hv
  rcases List.mem_map.mp hv with ⟨u, hu, rfl⟩
  exact originalSourceUnitNormal_Q_one u (hall u hu)

/-- Transporting the pulled-back list forwards preserves the
ENTIRE ordered list of source axes, not merely its span or set. -/
theorem originalSourceUnitNormalList_roundtrip (l : List Euc48) :
    (l.map originalSourceUnitNormal).map E = l := by
  induction l with
  | nil => rfl
  | cons u tail ih =>
      simp only [List.map_cons, originalSourceUnitNormal_roundtrip, ih]

#print axioms originalSourceUnitNormal
#print axioms originalSourceUnitNormal_roundtrip
#print axioms originalSourceUnitNormal_Q_one
#print axioms originalSourceUnitNormalList_all_Q_one
#print axioms originalSourceUnitNormalList_roundtrip

end
end FCP.BFSSS1V52K1D18V7M
