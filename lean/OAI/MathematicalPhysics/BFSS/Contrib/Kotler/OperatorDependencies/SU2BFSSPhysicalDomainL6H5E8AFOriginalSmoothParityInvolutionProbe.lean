import OAI.MathematicalPhysics.BFSS.Core

/-!
# L6H5E8AF — actual original BFSS smooth-core spatial parity

The gamma-orientation/charge-split source certificates AD/AE prove that
gamma_i -> -gamma_i negates ONLY the original charge kinetic part.
Here the analytic counterpart is a genuine parity map on the actual
upstream TestFunction SmoothCore N, not a surrogate compactly supported
function class. Construction must prove ContDiff and HasCompactSupport
under inversion of all nine-times-color bosonic coordinates.

The theorem is PROSPECTIVE until the strict original-source CI gate.
It does not yet establish derivative conjugation, physical gauge
invariance, graph closures, Hamiltonian domains, or a manuscript bridge.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AF
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData

/-- Pull back a source test function along the real inversion x |-> -x,
preserving compact support and all derivatives. -/
noncomputable def originalSmoothParityFun {N : ℕ}
    (f : SmoothCore N) : SmoothCore N where
  toFun := fun x => f (-x)
  contDiff' := by
    exact f.contDiff.comp (contDiff_id.neg)
  hasCompactSupport' := by
    change HasCompactSupport
      (f ∘ (Homeomorph.neg (Boson N)))
    exact f.hasCompactSupport.comp_homeomorph _
  tsupport_subset' := by
    intro x hx
    trivial

/-- Actual source SmoothCore N complex-linear spatial inversion. -/
noncomputable def originalSmoothParity {N : ℕ} :
    SmoothCore N →ₗ[ℂ] SmoothCore N where
  toFun := originalSmoothParityFun
  map_add' f g := by
    apply DFunLike.ext
    intro x
    rfl
  map_smul' c f := by
    apply DFunLike.ext
    intro x
    rfl

theorem originalSmoothParity_apply {N : ℕ}
    (f : SmoothCore N) (x : Boson N) :
    originalSmoothParity f x = f (-x) := rfl

/-- Full inversion twice is literally the identity on the original
smooth test core; this is not an assumed parity operator. -/
theorem originalSmoothParity_involutive {N : ℕ} :
    (originalSmoothParity (N := N)).comp originalSmoothParity =
      (LinearMap.id : SmoothCore N →ₗ[ℂ] SmoothCore N) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change f (-(-x)) = f x
  simp

/-- Every exact original BFSS position multiplier changes sign under
the actual 27-coordinate (for N=2) parity pullback. -/
theorem originalSmoothParity_position {N : ℕ}
    (i : SpaceIndex) (A : ColorIndex N) :
    (originalSmoothParity (N := N)).comp (position i A) =
      -((position i A).comp originalSmoothParity) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change ((((-x) (i, A) : ℝ) : ℂ) • f (-x)) =
    -((((x (i, A) : ℝ) : ℂ) • f (-x)))
  simp

/-- Source fermion operators act fiberwise and therefore commute with
inversion of bosonic spatial coordinates. -/
theorem originalSmoothParity_fermionAction {N : ℕ}
    (M : AlgebraData N) (β : SpinIndex) (A : ColorIndex N) :
    (originalSmoothParity (N := N)).comp (M.fermionAction β A) =
      (M.fermionAction β A).comp originalSmoothParity := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change M.theta β A (f (-x)) = M.theta β A (f (-x))
  rfl

#print axioms originalSmoothParityFun
#print axioms originalSmoothParity
#print axioms originalSmoothParity_apply
#print axioms originalSmoothParity_involutive
#print axioms originalSmoothParity_position
#print axioms originalSmoothParity_fermionAction

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AF
