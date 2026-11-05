import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M3BOriginalComplexCliffordSimpleModuleProbe
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
S1V52-M3C — True ORIGINAL 48-complex-Clifford Fock action:
Schur's scalar-commutant and finite-generation Jacobson prerequisites.

Exactly the M3B-qualified source Module A V action and its scalar tower
and IsSimpleModule theorem are installed. There is NO alternate Fock
representation, no assumed scalar commutant, and no surjectivity assertion.
The original independent manuscript-module comparison remains OPEN.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52M3C
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V52M3B

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev A := CliffordAlgebra (Q.baseChange ℂ)
private abbrev V := Fermion 2

local instance : Module A V :=
  originalComplexCliffordFockModule
local instance : IsScalarTower ℂ A V :=
  originalComplexCliffordFockModule_scalarTower
local instance : IsSimpleModule A V :=
  originalComplexCliffordFockModule_simple

/-- Schur: every A-linear endomorphism of the exact ORIGINAL Fock
representation is a complex scalar, with existence AND uniqueness. -/
theorem originalComplexCliffordFock_scalarCommutant :
    Function.Bijective (algebraMap ℂ (Module.End A V)) := by
  exact IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ

/-- The original finite-dimensional Fock module is finitely generated
over its actual ring of A-linear endomorphisms. This is the precise
Module.Finite hypothesis used by pinned Mathlib Jacobson density. -/
theorem originalComplexCliffordFock_finiteOverEnd :
    Module.Finite (Module.End A V) V := by
  exact Module.Finite.of_restrictScalars_finite ℂ (Module.End A V) V

#print axioms originalComplexCliffordFock_scalarCommutant
#print axioms originalComplexCliffordFock_finiteOverEnd

end
end FCP.BFSSS1V52M3C
