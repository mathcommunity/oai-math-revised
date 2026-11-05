import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPairedSpin9FourIndexRHSTransportProbe

/-!
K1D18V9H — exact generator-level preservation of the native
nine-index matrix product commutator by the accepted real LinearMap.

This stage combines four individually accepted source exact results:
V8W input F_rs commutator, V9G transport of its four-index RHS,
V9B generator agreement, and V8R original paired 48-real
normalized H_rs commutator. Every repeated index is included.

This is a theorem for coordinate generators, not yet preservation
of arbitrary skew-input brackets or a constructed so(9) LieHom.
Global Spin(9), Fock action and BFSS physics remain separate.
-/

set_option autoImplicit false

namespace FCP.BFSSPairedSpin9Plane
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0

/-- Exact source-native generator commutator preservation, including
all spatial-index coincidences and original paired Fock labels. -/
theorem coordinateToPairedLinearMap_generator_commutator
    (r s t u : SpaceIndex) :
    coordinateToPairedLinearMap
      (coordinatePlane9 r s * coordinatePlane9 t u -
       coordinatePlane9 t u * coordinatePlane9 r s) =
      coordinateToPairedLinearMap (coordinatePlane9 r s) *
        coordinateToPairedLinearMap (coordinatePlane9 t u) -
      coordinateToPairedLinearMap (coordinatePlane9 t u) *
        coordinateToPairedLinearMap (coordinatePlane9 r s) := by
  rw [coordinatePlane9_universal_four_index_bracket r s t u,
    coordinateToPairedLinearMap_fourIndexRHS r s t u,
    coordinateToPairedLinearMap_coordinatePlane r s,
    coordinateToPairedLinearMap_coordinatePlane t u,
    normalizedPairedPlane_universal_four_index_bracket r s t u]

#print axioms coordinateToPairedLinearMap_generator_commutator

end
end FCP.BFSSPairedSpin9Plane
