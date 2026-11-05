import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.FCPIndependentKineticCharge

/-!
M4E4A — genuinely independent smooth position multiplication on the
E-valued BFSS compactly supported test-function core.

The scalar test-function multiplier is built directly on E-valued
functions. The independent position operator uses the original bosonic
coordinate geometry but NO J, original Fock operator, source charge,
or transported definition. Only the theorem relates it to the pinned
original AlgebraData.position on smooth test functions.

This is the position factor for the separate cubic supercharge gate.
No cubic expression, whole supercharge, graph domain, or spectrum
is asserted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace FCP.IndependentSmoothSupercharge
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.IndependentSmoothCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Independent smooth scalar multiplication on the actual E-valued
test-function space, with compact support inherited from the input. -/
def independentSmoothMultiplier
    (g : Boson 2 → ℂ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    IndependentTestCore E →ₗ[ℂ] IndependentTestCore E where
  toFun f := {
    toFun := fun x => g x • f x
    contDiff' := hg.smul f.contDiff
    hasCompactSupport' := by
      change HasCompactSupport (g • (f : Boson 2 → E))
      exact HasCompactSupport.smul_left (f := g) f.hasCompactSupport
    tsupport_subset' := by intro x hx; trivial
  }
  map_add' f k := by
    apply DFunLike.ext
    intro x
    change g x • (f x + k x) = g x • f x + g x • k x
    exact smul_add _ _ _
  map_smul' c f := by
    apply DFunLike.ext
    intro x
    change g x • (c • f x) = c • (g x • f x)
    exact smul_comm _ _ _

/-- The independent position operator multiplies by the real bosonic
coordinate embedded into ℂ, on the E-valued fiber directly. -/
def independentPosition
    (i : SpaceIndex) (A : ColorIndex 2) :
    IndependentTestCore E →ₗ[ℂ] IndependentTestCore E :=
  independentSmoothMultiplier
    (fun x => (coordinate i A x : ℂ))
    (Complex.ofRealCLM.contDiff.comp (coordinate_contDiff i A))

theorem independentPosition_apply
    (i : SpaceIndex) (A : ColorIndex 2)
    (f : IndependentTestCore E) (x : Boson 2) :
    independentPosition i A f x = (coordinate i A x : ℂ) • f x := by
  rfl

/-- The independent E-valued position and the literal source position
commute with the true smooth fiber map, by complex linearity of J. -/
theorem independentPosition_intertwining
    (J : E ≃ₗᵢ[ℂ] Fermion 2)
    (i : SpaceIndex) (A : ColorIndex 2)
    (f : IndependentTestCore E) :
    independentSmoothTransport J (independentPosition i A f) =
      position i A (independentSmoothTransport J f) := by
  apply DFunLike.ext
  intro x
  change J ((coordinate i A x : ℂ) • f x) =
    (coordinate i A x : ℂ) • J (f x)
  exact map_smul J (coordinate i A x : ℂ) (f x)

#print axioms independentSmoothMultiplier
#print axioms independentPosition
#print axioms independentPosition_apply
#print axioms independentPosition_intertwining

end
end FCP.IndependentSmoothSupercharge
