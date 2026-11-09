import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AFOriginalSmoothParityInvolutionProbe

/-!
# L6H5E8AG — derivative sign for genuine original TestFunction parity

The accepted AF source map P on SmoothCore N is f(x) -> f(-x).
This lemma is the exact derivative half of source gamma-orientation
charge conjugation. It uses ONLY pinned upstream AlgebraData.
coordinateDerivative_apply, the differentiability of the actual
SmoothCore f and Mathlib fderiv_comp, not a surrogate differential
operator or invented parity action.

PROSPECTIVE until exact-source Lean CI; no Hamiltonian domain or
manuscript representation equivalence follows from merely writing
this statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AG
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AF

/-- The actual source coordinate derivative anticommutes with parity
for every original space/color index, on the original SmoothCore N. -/
theorem originalSmoothParity_coordinateDerivative {N : ℕ}
    (i : SpaceIndex) (A : ColorIndex N) :
    (originalSmoothParity (N := N)).comp (coordinateDerivative i A) =
      -((coordinateDerivative i A).comp originalSmoothParity) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  change (coordinateDerivative i A f) (-x) =
    -((coordinateDerivative i A (originalSmoothParity f)) x)
  rw [coordinateDerivative_apply, coordinateDerivative_apply]
  change
    fderiv ℝ (f : Boson N → Fermion N) (-x)
      (EuclideanSpace.single (i, A) 1) =
    -(fderiv ℝ (fun y : Boson N => f (-y)) x
      (EuclideanSpace.single (i, A) 1))
  have hf : DifferentiableAt ℝ (f : Boson N → Fermion N) (-x) :=
    (f.contDiff.differentiable (by simp)).differentiableAt
  have hneg : DifferentiableAt ℝ (fun y : Boson N => -y) x :=
    differentiableAt_id.neg
  have hchain :
      fderiv ℝ (fun y : Boson N => f (-y)) x =
        (fderiv ℝ (f : Boson N → Fermion N) (-x)).comp
          (fderiv ℝ (fun y : Boson N => -y) x) := by
    simpa only [Function.comp_def] using (fderiv_comp x hf hneg)
  have hv := congrArg
    (fun L : Boson N →L[ℝ] Fermion N =>
      L (EuclideanSpace.single (i, A) 1)) hchain
  have hsource :
      fderiv ℝ (fun y : Boson N => f (-y)) x
          (EuclideanSpace.single (i, A) 1) =
        -(fderiv ℝ (f : Boson N → Fermion N) (-x)
          (EuclideanSpace.single (i, A) 1)) := by
    -- Pin the Fréchet derivative of x ↦ -x explicitly rather than
    -- asking simp to recognize an eta-expanded negative identity map.
    have hnegder :
        fderiv ℝ (fun y : Boson N => -y) x =
          -(ContinuousLinearMap.id ℝ (Boson N)) := by
      calc
        fderiv ℝ (fun y : Boson N => -y) x =
            -(fderiv ℝ (id : Boson N → Boson N) x) := by
          exact (fderiv_fun_neg (𝕜 := ℝ)
            (f := id) (x := x))
        _ = -(ContinuousLinearMap.id ℝ (Boson N)) := by
          rw [fderiv_id]
    simpa only [ContinuousLinearMap.comp_apply, hnegder, neg_apply,
      ContinuousLinearMap.id_apply, map_neg] using hv
  rw [hsource]
  simp

#print axioms originalSmoothParity_coordinateDerivative
#check @originalSmoothParity_coordinateDerivative

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AG
