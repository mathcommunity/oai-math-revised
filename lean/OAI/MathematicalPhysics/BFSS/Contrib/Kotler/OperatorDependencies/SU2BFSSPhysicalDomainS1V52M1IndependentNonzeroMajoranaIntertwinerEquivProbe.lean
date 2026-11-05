import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG1APairedThetaProbe

/-!
S1V52-M1: a NONZERO generator-intertwining linear map from an
INDEPENDENT irreducible complex 48-Majorana module to the accepted
ORIGINAL Fock module is automatically a complex-linear equivalence.

This is a strict, falsifiable sublemma of Issue #28's manuscript-to-source
realization problem, NOT a proof that any such nonzero map exists.
The independent module E is a genuine variable Type, NOT Fermion 2.
The 48 operators on E and their irreducibility are hypotheses.
The original pairedTheta irreducibility is a separately kernel-qualified
original source theorem (G1A), not assumed.

Both kernel and range invariance are proved from exact generator
intertwining, so there is no finrank equality assumption, no phase
choice, no surjectivity hypothesis and no circular assumed equivalence.
Unitarity, existence of the nonzero generator map, Spin48 action,
smooth core and unbounded domain transport are still OPEN.
-/

set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.BFSSS1V52M1
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Any nonzero exact 48-generator complex-linear intertwiner from an
independent IRREDUCIBLE complex module to the ORIGINAL irreducible
BFSS source Fock module is bijective, yielding an actual equivalence.
The map's existence and Hilbert unitarity are not asserted. -/
theorem independent_nonzero_majorana_intertwiner_equiv
    (theta : SpinIndex → ColorIndex 2 → E →ₗ[ℂ] E)
    (hirr : ∀ W : Submodule ℂ E,
      (∀ α A, ∀ w ∈ W, theta α A w ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (T₀ : E →ₗ[ℂ] Fermion 2)
    (hT : ∀ (α : SpinIndex) (A : ColorIndex 2) (v : E),
      T₀ (theta α A v) = pairedTheta α A (T₀ v))
    (v₀ : E) (hnonzero : T₀ v₀ ≠ 0) :
    ∃ T : E ≃ₗ[ℂ] Fermion 2,
      ∀ (α : SpinIndex) (A : ColorIndex 2) (v : E),
        T (theta α A v) = pairedTheta α A (T v) := by
  have hkerStable :
      ∀ α A, ∀ w ∈ T₀.ker, theta α A w ∈ T₀.ker := by
    intro α A w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [hT α A w, hw, map_zero]
  have hkerNeTop : T₀.ker ≠ ⊤ := by
    intro htop
    have hv : v₀ ∈ T₀.ker := by
      rw [htop]
      exact Submodule.mem_top
    exact hnonzero (LinearMap.mem_ker.mp hv)
  have hker : T₀.ker = ⊥ := by
    rcases hirr T₀.ker hkerStable with hbot | htop
    · exact hbot
    · exact (hkerNeTop htop).elim
  have hinj : Function.Injective T₀ :=
    LinearMap.ker_eq_bot.mp hker
  have hrangeStable :
      ∀ α A, ∀ w ∈ T₀.range, pairedTheta α A w ∈ T₀.range := by
    intro α A w hw
    rcases hw with ⟨x, rfl⟩
    exact ⟨theta α A x, hT α A x⟩
  have hrangeNeBot : T₀.range ≠ ⊥ := by
    intro hbot
    have hv : T₀ v₀ ∈ T₀.range := ⟨v₀, rfl⟩
    rw [hbot] at hv
    exact hnonzero ((Submodule.mem_bot ℂ).mp hv)
  have hrange : T₀.range = ⊤ := by
    rcases pairedTheta_irreducible T₀.range hrangeStable with hbot | htop
    · exact (hrangeNeBot hbot).elim
    · exact htop
  have hsurj : Function.Surjective T₀ :=
    LinearMap.range_eq_top.mp hrange
  let T : E ≃ₗ[ℂ] Fermion 2 :=
    LinearEquiv.ofBijective T₀ ⟨hinj, hsurj⟩
  refine ⟨T, ?_⟩
  intro α A v
  exact hT α A v

#print axioms independent_nonzero_majorana_intertwiner_equiv

end
end FCP.BFSSS1V52M1
