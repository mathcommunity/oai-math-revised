import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V34GenuineSpin48QuadraticIsometryEquivProbe
import Mathlib.Algebra.Module.Equiv.Basic

/-!
S1V35 — ACTUAL source-sized Clifford Spin48 group homomorphism into
48-real linear automorphisms, using exactly S1V29–S1V34 axiom-clean
source mathematical facts.

Pinned Mathlib's LinearEquiv.automorphismGroup multiplication is
f * g = g.trans f, hence (f*g) v = f (g v). This composition order is
the same as the actual Clifford group action, NOT the reverse-ordered
IsometryEquiv.trans API. No surrogate SO48 map or arbitrary conjugation
representation is introduced.

THREE NEW UNCOMPILED roots until strict CI. Source Q invariance
is accepted separately from S1V33–34. No det +1, Spin→SO48 codomain
or covering topology/global lift is claimed by these source declarations.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V35
noncomputable section

open FCP.BFSSS1V0
open FCP.BFSSS1V34

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Actual source Clifford Spin48 identity acts as the identity
invertible real-linear operator on ALL original 48-real vectors. -/
theorem sourceSpin48LinearEquiv_one :
    sourceSpin48LinearEquiv (1 : spinGroup Q) =
      (1 : Source48Vector ≃ₗ[ℝ] Source48Vector) := by
  apply LinearEquiv.ext
  intro v
  change FCP.BFSSS1V31.sourceSpin48VectorAction (1 : spinGroup Q) v = v
  exact FCP.BFSSS1V32.sourceSpin48VectorAction_one v

/-- The true original Spin48 group multiplication induces genuine
real-linear operator multiplication, NOT reversed composition. -/
theorem sourceSpin48LinearEquiv_mul (s t : spinGroup Q) :
    sourceSpin48LinearEquiv (s * t) =
      sourceSpin48LinearEquiv s * sourceSpin48LinearEquiv t := by
  apply LinearEquiv.ext
  intro v
  change FCP.BFSSS1V31.sourceSpin48VectorAction (s * t) v =
    FCP.BFSSS1V31.sourceSpin48VectorAction s
      (FCP.BFSSS1V31.sourceSpin48VectorAction t v)
  exact FCP.BFSSS1V32.sourceSpin48VectorAction_mul s t v

/-- GENUINE source Clifford Spin48 to original 48-real GL group
homomorphism; the image preserves exact source Q by S1V33, but det+1,
SO48, covering and lifting are NOT asserted here. -/
noncomputable def sourceSpin48LinearEquivHom :
    spinGroup Q →* (Source48Vector ≃ₗ[ℝ] Source48Vector) where
  toFun := sourceSpin48LinearEquiv
  map_one' := sourceSpin48LinearEquiv_one
  map_mul' := sourceSpin48LinearEquiv_mul

#print axioms sourceSpin48LinearEquiv_one
#print axioms sourceSpin48LinearEquiv_mul
#print axioms sourceSpin48LinearEquivHom

end
end FCP.BFSSS1V35
