import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9SkewCoordinatePlaneSpanningProbe

/-!
K1D18V9G — typed source-exact transport of the universal four-index
coordinate bracket RHS through the accepted real LinearMap.

This bounded stage transports the four-delta RHS from the original
nine-index coordinate-plane carrier to the original Fock-paired
48-real normalized generator carrier. It uses the accepted V9B
generator agreement and LinearMap add/sub/neg laws.

The actual generator commutator preservation and arbitrary skew
input commutator preservation remain separate obligations.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- Exact conditional coordinate-generator transport on native
nine-index matrices, including both branches of the condition. -/
theorem coordinateToPairedLinearMap_conditional_plane
    (p : Prop) [Decidable p] (r s : SpaceIndex) :
    coordinateToPairedLinearMap
      (if p then coordinatePlane9 r s else 0) =
        (if p then normalizedPairedPlane r s else 0) := by
  by_cases hp : p
  · simp only [hp, ite_true]
    exact coordinateToPairedLinearMap_coordinatePlane r s
  · simp [hp]

/-- The full native four-Kronecker-delta input bracket RHS
transports to precisely the accepted original paired 48-real
normalized four-index RHS, including all index coincidences. -/
theorem coordinateToPairedLinearMap_fourIndexRHS
    (r s t u : SpaceIndex) :
    coordinateToPairedLinearMap (coordinateFourIndexRHS r s t u) =
      normalizedFourIndexRHS r s t u := by
  unfold coordinateFourIndexRHS normalizedFourIndexRHS
  simp only [map_add, map_sub, map_neg]
  rw [coordinateToPairedLinearMap_conditional_plane (s = u) r t,
    coordinateToPairedLinearMap_conditional_plane (s = t) r u,
    coordinateToPairedLinearMap_conditional_plane (r = t) s u,
    coordinateToPairedLinearMap_conditional_plane (r = u) s t]

#print axioms coordinateToPairedLinearMap_conditional_plane
#print axioms coordinateToPairedLinearMap_fourIndexRHS

end
end FCP.BFSSPairedSpin9Plane
