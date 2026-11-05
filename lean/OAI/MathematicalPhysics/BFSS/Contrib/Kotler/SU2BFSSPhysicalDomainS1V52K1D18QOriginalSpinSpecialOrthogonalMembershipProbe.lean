import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D18POriginalSpinQuadraticIsometryDetOneProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D15OriginalSpin48QuadraticPreservationProbe

/-!
K1D18Q: exact original-source quadratic-preserving GL subgroup,
determinant-one intersection, and genuine Spin48 membership.
No substitute action, alternative 48-vector form, Spin word
factorization, SO-group map, surjectivity, covering, Spin9
global covariance or BFSS spectral claim. Candidate only.
-/
set_option autoImplicit false

namespace FCP.BFSSS1V52K1D18Q
noncomputable section
open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev GL48 := Source48Vector ≃ₗ[ℝ] Source48Vector

/-- Abstract form-preserving automorphisms. This generic lemma is
proved without unfolding or even referencing the large source48Quadratic. -/
private noncomputable def quadraticPreservingGLGeneric
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : QuadraticForm ℝ V) : Subgroup (V ≃ₗ[ℝ] V) where
  carrier := {f | ∀ v, q (f v) = q v}
  one_mem' := by
    intro v
    have hOne : ((1 : V ≃ₗ[ℝ] V) v) = v := rfl
    exact congrArg q hOne
  mul_mem' := by
    intro f g hf hg v
    have hMul : ((f * g : V ≃ₗ[ℝ] V) v) = f (g v) := rfl
    have hQuad : q (f (g v)) = q v :=
      (hf (g v)).trans (hg v)
    exact (congrArg q hMul).trans hQuad
  inv_mem' := by
    intro f hf v
    have hInv : ((f⁻¹ : V ≃ₗ[ℝ] V) v) = f.symm v := rfl
    have hApply : f (f.symm v) = v := f.apply_symm_apply v
    have hQuad : q (f.symm v) = q v :=
      (hf (f.symm v)).symm.trans (congrArg q hApply)
    exact (congrArg q hInv).trans hQuad

/-- An arbitrary abstract quadratic isometry belongs to that form's
preserving GL subgroup by its native IsometryEquiv structure field. -/
private theorem quadraticPreservingGLGeneric_mem_of_isometry
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : QuadraticForm ℝ V) (i : q.IsometryEquiv q) :
    (i : V ≃ₗ[ℝ] V) ∈ quadraticPreservingGLGeneric q := by
  intro v
  exact i.map_app' v

/-- Specialize the abstract construction to the ORIGINAL Fin24×Fin2
source vectors and source48Quadratic, without changing either. -/
noncomputable def source48QuadraticPreservingGL : Subgroup GL48 :=
  quadraticPreservingGLGeneric source48Quadratic

/-- Pinned Mathlib's actual invertible determinant character. -/
noncomputable def source48DetCharacter : GL48 →* ℝˣ :=
  LinearEquiv.det

/-- Original quadratic preservation AND real determinant one. -/
noncomputable def source48SpecialOrthogonalGL : Subgroup GL48 :=
  source48QuadraticPreservingGL ⊓ source48DetCharacter.ker

/-- Generic source-exact bridge: the linear part of an existing
isometry preserves the original quadratic form, by its source field. -/
theorem source48QuadraticPreservingGL_mem_of_isometry
    (i : Q.IsometryEquiv Q) :
    (i : GL48) ∈ source48QuadraticPreservingGL := by
  exact quadraticPreservingGLGeneric_mem_of_isometry source48Quadratic i

/-- Explicit same-action equality, using the accepted K1D16 source
linear-equivalence equality, not an assumed replacement action. -/
theorem originalSourceSpin48_isometry_linearRepresentation_eq
    (s : spinGroup Q) :
    (FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s :
       GL48) =
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation s := by
  exact FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry_underlyingLinearEquiv s

/-- The original Spin48 action lands in the exact source special
orthogonal subgroup, via the accepted isometry structure and P. -/
theorem originalSourceSpin48_mem_sourceSO (s : spinGroup Q) :
    FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation s ∈
      source48SpecialOrthogonalGL := by
  have hIso :
      (FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s :
        GL48) ∈ source48QuadraticPreservingGL :=
    source48QuadraticPreservingGL_mem_of_isometry
      (FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry s)
  have hPreserving :
      FCP.BFSSS1V52K1D13.originalSourceSpin48LinearRepresentation s ∈
        source48QuadraticPreservingGL := by
    rw [← originalSourceSpin48_isometry_linearRepresentation_eq s]
    exact hIso
  constructor
  · exact hPreserving
  · change source48DetCharacter
      (FCP.BFSSS1V52K1D13.originalSourceSpin48LinearEquiv s) = 1
    apply Units.ext
    change ((LinearEquiv.det
      (FCP.BFSSS1V52K1D13.originalSourceSpin48LinearEquiv s) : ℝˣ) : ℝ) = 1
    rw [LinearEquiv.coe_det,
      ← FCP.BFSSS1V52K1D16.originalSourceSpin48QuadraticIsometry_underlyingLinearEquiv]
    exact FCP.BFSSS1V52K1D18P.originalSourceSpin48_quadraticIsometry_det_one s

#print axioms source48QuadraticPreservingGL
#print axioms source48DetCharacter
#print axioms source48SpecialOrthogonalGL
#print axioms source48QuadraticPreservingGL_mem_of_isometry
#print axioms originalSourceSpin48_isometry_linearRepresentation_eq
#print axioms originalSourceSpin48_mem_sourceSO

end
end FCP.BFSSS1V52K1D18Q
