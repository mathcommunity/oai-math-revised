import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M3AOriginalComplexCliffordActionImageIrreducibilityProbe
import Mathlib.RingTheory.SimpleModule.Basic

/-!
S1V52-M3B — Exact ORIGINAL complexified Clifford module structure and
simple-module bridge for original finite 24-mode Fock space.

These statements do not assert surjectivity onto the Fock endomorphism
algebra. They discharge its indispensable source-specific module-action
and irreducibility hypotheses while preserving the ORIGINAL M2 algebra
homomorphism and the M3A accepted 48-Majorana invariance result.

Only the exact original source action is installed. The separate
independent manuscript module and Hilbert unitary remain unconstructed.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52M3B
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V52M2
open FCP.BFSSS1V52M3A

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev A := CliffordAlgebra (Q.baseChange ℂ)
private abbrev V := Fermion 2

/-- Action of the actual M2 complex Clifford algebra homomorphism on
the original 24-mode Fock space; no surrogate representation. -/
noncomputable def originalComplexCliffordFockModule : Module A V :=
  Module.compHom V originalComplexCliffordFockAlgHom.toRingHom

/-- Definitional agreement between the module action and the accepted
original M2 operator algebra homomorphism. -/
theorem originalComplexCliffordFockModule_smul (a : A) (v : V) :
    letI : Module A V := originalComplexCliffordFockModule
    a • v = originalComplexCliffordFockAlgHom a v := by
  rfl

/-- The newly installed A-action is compatible with the ORIGINAL
complex scalar action on Fock space. -/
theorem originalComplexCliffordFockModule_scalarTower :
    letI : Module A V := originalComplexCliffordFockModule
    IsScalarTower ℂ A V := by
  letI : Module A V := originalComplexCliffordFockModule
  refine ⟨?_⟩
  intro c a v
  change (originalComplexCliffordFockAlgHom (c • a)) v =
    c • (originalComplexCliffordFockAlgHom a v)
  simpa only [map_smul, ContinuousLinearMap.smul_apply]

/-- Original M3A exact image irreducibility, transported to an
IsSimpleModule proof for this very same complex Clifford algebra action. -/
theorem originalComplexCliffordFockModule_simple :
    letI : Module A V := originalComplexCliffordFockModule
    IsSimpleModule A V := by
  letI : Module A V := originalComplexCliffordFockModule
  letI : IsScalarTower ℂ A V :=
    originalComplexCliffordFockModule_scalarTower
  classical
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  have hstable :
      ∀ x : A, ∀ w ∈ W.restrictScalars ℂ,
        originalComplexCliffordFockAlgHom x w ∈ W.restrictScalars ℂ := by
    intro x w hw
    change w ∈ W at hw
    change x • w ∈ W
    exact W.smul_mem x hw
  have h := originalComplexCliffordFock_image_irreducible
    (W.restrictScalars ℂ) hstable
  simpa only [Submodule.restrictScalars_eq_bot_iff,
    Submodule.restrictScalars_eq_top_iff] using h

#print axioms originalComplexCliffordFockModule
#print axioms originalComplexCliffordFockModule_smul
#print axioms originalComplexCliffordFockModule_scalarTower
#print axioms originalComplexCliffordFockModule_simple

end
end FCP.BFSSS1V52M3B
