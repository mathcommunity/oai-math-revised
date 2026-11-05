import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M3COriginalCliffordFockSchurAndFiniteProbe
import Mathlib.RingTheory.SimpleModule.Basic

/-!
M3D — exact source Clifford Fock endomorphism FULL IMAGE.

Use the qualified M3B *actual* complexified Clifford module,
the M3C true Schur scalar commutant and actual endomorphism-ring
finite-generation, and pinned Jacobson density, to construct a
preimage for EVERY complex-linear continuous Fock operator.

Do not replace this source A-action by an isomorphic abstract matrix
representation. Does not construct the independent manuscript module.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52M3D
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V52M2
open FCP.BFSSS1V52M3B
open FCP.BFSSS1V52M3C

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev A := CliffordAlgebra (Q.baseChange ℂ)
private abbrev V := Fermion 2
private abbrev FockOp := V →L[ℂ] V

local instance : Module A V :=
  originalComplexCliffordFockModule
local instance : IsScalarTower ℂ A V :=
  originalComplexCliffordFockModule_scalarTower
local instance : IsSimpleModule A V :=
  originalComplexCliffordFockModule_simple

private abbrev B := Module.End A V

local instance : Module.Finite B V :=
  originalComplexCliffordFock_finiteOverEnd

/-- Every complex-linear continuous operator of the ORIGINAL Fock space
is in the exact original complexified 48-Clifford image. -/
theorem originalComplexCliffordFock_fullImage :
    Function.Surjective
      (originalComplexCliffordFockAlgHom : A → FockOp) := by
  intro f
  let g : Module.End B V :=
    { toFun := f
      map_add' := by intro x y; exact f.map_add x y
      map_smul' := by
        intro b v
        obtain ⟨c, rfl⟩ := originalComplexCliffordFock_scalarCommutant.2 b
        simpa only [RingHom.id_apply, algebraMap_smul] using f.map_smul c v }
  obtain ⟨a, ha⟩ :=
    (Module.Finite.toModuleEnd_moduleEnd_surjective
      (R := A) (M := V)) g
  refine ⟨a, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  have hv := LinearMap.congr_fun ha v
  change a • v = f v at hv
  change (originalComplexCliffordFockAlgHom a) v = f v at hv
  exact hv

#print axioms originalComplexCliffordFock_fullImage

end
end FCP.BFSSS1V52M3D
