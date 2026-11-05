import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K8E1MasslessPotentialParityProbe

/-!
# BFSS SU(2) G4-K8E2 — oddness of the actual kinetic first-order term

Gate #155 (G4-K8E1) proved that the SAME exact Gauss-invariant,
nonzero, smooth SU(2) radial BFSS state is even under x ↦ -x
and that the true source massless potential multiplication
section is even for every coupling h.

This candidate proves the complementary oddness of the ORIGINAL
source kinetic term. Use an ABSTRACT smooth even function and
abstract source-typed continuous-linear symbol while proving the
functional/derivative lemmas. Specialize only at the final stages
to the real pinned MixedEnergy.delta and MixedEnergy.firstOrder
acting on the original radialBumpSmoothCore.

A pointwise odd/even separation together with the previously
proven nonzero kinetic FullL2 charge may later yield
noncancellation at h=1,m=0. That NONCANCELLATION and
interacting h=1 strict energy are NOT proved here. No gap,
ground-state, energy infimum or spectrum claim is made.
-/

namespace FCP.BFSSSU2GaugeG4K8E2
noncomputable section

open scoped BigOperators
open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4K3
open FCP.BFSSSU2GaugeG4K8E1

/-- For a differentiable EVEN function, its REAL Frechet derivative
is ODD as evaluated on every fixed direction.
Derive from the pinned Mathlib chain rule, keeping f abstract. -/
private theorem abstractFderivEven_odd_apply
    (f : Boson 2 → Fermion 2)
    (hf : Differentiable ℝ f)
    (heven : ∀ y : Boson 2, f (-y) = f y)
    (x v : Boson 2) :
    fderiv ℝ f (-x) v = -(fderiv ℝ f x v) := by
  have hfun : (fun y : Boson 2 => f (-y)) = f := by
    funext y
    exact heven y
  have hcomp :
      fderiv ℝ (fun y : Boson 2 => f (-y)) x =
        (fderiv ℝ f (-x)).comp
          (-(ContinuousLinearMap.id ℝ (Boson 2))) := by
    have hc := fderiv_comp x (hf (-x))
      (by fun_prop : DifferentiableAt ℝ (fun y : Boson 2 => -y) x)
    change fderiv ℝ (fun y : Boson 2 => f (-y)) x =
      (fderiv ℝ f (-x)).comp
        (fderiv ℝ (fun y : Boson 2 => -y) x) at hc
    have hneg :
        fderiv ℝ (fun y : Boson 2 => -y) x =
          -(ContinuousLinearMap.id ℝ (Boson 2)) := by
      calc
        fderiv ℝ (fun y : Boson 2 => -y) x =
            -fderiv ℝ (fun y : Boson 2 => y) x :=
          (fderiv_fun_neg (𝕜 := ℝ)
            (f := fun y : Boson 2 => y) (x := x))
        _ = -(ContinuousLinearMap.id ℝ (Boson 2)) := by
          rw [fderiv_fun_id]
    rw [hneg] at hc
    exact hc
  rw [hfun] at hcomp
  have happ := congrArg
    (fun L : Boson 2 →L[ℝ] Fermion 2 => L (-v)) hcomp.symm
  simpa only [ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.id_apply, map_neg, neg_neg] using happ

/-- Pinned source MixedEnergy.delta is the coordinate directional
derivative. Evenness of the actual physical state forces its oddness. -/
theorem physicalDelta_odd
    (p : SpaceIndex × ColorIndex 2) (x : Boson 2) :
    MixedEnergy.delta p radialBumpSmoothCore (-x) =
      -(MixedEnergy.delta p radialBumpSmoothCore x) := by
  rw [MixedEnergy.delta_apply, MixedEnergy.delta_apply]
  exact abstractFderivEven_odd_apply
    (radialBumpSmoothCore : Boson 2 → Fermion 2)
    (radialBumpSmoothCore.contDiff.differentiable (by simp))
    physicalSmoothRadialState_even
    x (EuclideanSpace.single p 1)

/-- Abstract sum of pinned first-order operators:
an x-INDEPENDENT linear coefficient cannot change the oddness
of directional derivatives. Keep B an abstract source-typed
function, avoiding expansion of concrete fermion symbols. -/
private theorem abstractFirstOrder_odd
    (B : SpaceIndex × ColorIndex 2 → Fermion 2 →L[ℝ] Fermion 2)
    (f : SmoothCore 2)
    (hdelta : ∀ (p : SpaceIndex × ColorIndex 2) (x : Boson 2),
      MixedEnergy.delta p f (-x) = -(MixedEnergy.delta p f x))
    (x : Boson 2) :
    MixedEnergy.firstOrder B f (-x) =
      -(MixedEnergy.firstOrder B f x) := by
  rw [MixedEnergy.firstOrder_apply, MixedEnergy.firstOrder_apply]
  calc
    (∑ p : SpaceIndex × ColorIndex 2,
        B p (MixedEnergy.delta p f (-x))) =
      ∑ p : SpaceIndex × ColorIndex 2,
        B p (-(MixedEnergy.delta p f x)) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hdelta p x]
    _ = ∑ p : SpaceIndex × ColorIndex 2,
          -(B p (MixedEnergy.delta p f x)) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [map_neg]
    _ = -(∑ p : SpaceIndex × ColorIndex 2,
          B p (MixedEnergy.delta p f x)) := by
          rw [Finset.sum_neg_distrib]

/-- Exact ORIGINAL pinned kinetic first-order BFSS supercharge
is ODD on the SAME smooth Gauss-invariant radial trial state.
No source kinetic coefficient, fermion or field is redefined. -/
theorem physicalKineticFirstOrder_odd (α : SpinIndex) (x : Boson 2) :
    MixedEnergy.firstOrder
        (pairedAlgebraData.kineticSkewSymbol α)
        radialBumpSmoothCore (-x) =
      -(MixedEnergy.firstOrder
        (pairedAlgebraData.kineticSkewSymbol α)
        radialBumpSmoothCore x) := by
  exact abstractFirstOrder_odd
    (pairedAlgebraData.kineticSkewSymbol α)
    radialBumpSmoothCore
    (fun p y => physicalDelta_odd p y) x

#print axioms abstractFderivEven_odd_apply
#print axioms physicalDelta_odd
#print axioms abstractFirstOrder_odd
#print axioms physicalKineticFirstOrder_odd

end
end FCP.BFSSSU2GaugeG4K8E2
