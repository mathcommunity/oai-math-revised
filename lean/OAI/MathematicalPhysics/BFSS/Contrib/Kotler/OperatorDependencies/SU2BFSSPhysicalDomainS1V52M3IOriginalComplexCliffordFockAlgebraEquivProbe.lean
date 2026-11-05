import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M3HOriginalComplexCliffordFockFaithfulProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52M3DOriginalComplexCliffordFullFockImageProbe

/-!
S1V52M3I — strict-eligible but UNQUALIFIED source-only candidate
for an actual algebra equivalence from the ORIGINAL complexified
48-Majorana Clifford algebra to the full complex continuous-linear
endomorphism algebra of the ORIGINAL 24-mode Fock Hilbert space.

This is a conversion of the exact accepted M3D full-image theorem
plus the prospective M3H injectivity theorem using the pinned Mathlib
AlgEquiv.ofBijective constructor. Nothing is assumed about an
INDEPENDENT manuscript fermionic module, unitary intertwiner,
physical supercharges, unbounded operator domains, or BFSS spectrum.

Do NOT count this target, or launch its gate, before an independently
successful strict M3H parent source/axiom audit and qualified cache.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52M3I
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V52M2
open FCP.BFSSS1V52M3H

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev A := CliffordAlgebra (Q.baseChange ℂ)
private abbrev FockOp := Fermion 2 →L[ℂ] Fermion 2

/-- The exact original-source complex Clifford action is an actual
ℂ-algebra equivalence to every continuous linear source Fock operator,
with no arbitrary substitute matrices or assumed manuscript module. -/
noncomputable def originalComplexCliffordFockAlgEquiv : A ≃ₐ[ℂ] FockOp :=
  AlgEquiv.ofBijective
    (originalComplexCliffordFockAlgHom : A →ₐ[ℂ] FockOp)
    ⟨originalComplexCliffordFock_injective,
      FCP.BFSSS1V52M3D.originalComplexCliffordFock_fullImage⟩

/-- This actual source algebra equivalence is precisely the
previously accepted original complexified Clifford Fock action. -/
theorem originalComplexCliffordFockAlgEquiv_apply (a : A) :
    originalComplexCliffordFockAlgEquiv a =
      originalComplexCliffordFockAlgHom a :=
  rfl

#print axioms originalComplexCliffordFockAlgEquiv
#print axioms originalComplexCliffordFockAlgEquiv_apply

end
end FCP.BFSSS1V52M3I
