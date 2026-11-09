import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D0OriginalCliffordExteriorContractionTransportProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V38Original48PolarCoefficientBridgeProbe

/-! Owner import from FCP cc608e2282e1b32bb11bbb64424e4775b28138e2,
original source blob 46cd08ee5124dae7160f6fa2135b9b01c73b1030.
Only imports and this provenance comment are adapted. Definitions, theorem
statements and proof bodies below are source-exact. Local candidate only
until an independent owner strict gate passes. -/

/-!
K1D1 — original source polar half-coordinate vector yields exact real dual.

Reuses S1V38's five strictly accepted original weighted-sum-squares
polarization roots, not a substituted quadratic form or fabricated
coefficient theorem. Composes with K1D0 to show an original source
Spin48 trivial-action element is annihilated by EVERY individual
coordinate-dual exterior contraction.

This is NOT the still-open K1D2 full exterior finite-set coefficient
separation/common-kernel-scalar theorem. No two-sign kernel/cover/
global Spin9/physical spectral statement is asserted. Staged.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

namespace FCP.BFSSS1V52K1D1
noncomputable section
open FCP.BFSSS1V0
open Matrix

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- The real source half-unit coordinate vector is sent by the
ORIGINAL quadratic polar bilinear map to the literal coordinate dual. -/
theorem originalSourcePolar_halfSingle_eq_coordinateDual
    (j : Source48Label) :
    Q.polarBilin ((1 / 2 : ℝ) • (Pi.single j (1 : ℝ) : Source48Vector)) =
      (LinearMap.proj j : Module.Dual ℝ Source48Vector) := by
  apply LinearMap.ext
  intro v
  change QuadraticMap.polar Q
    ((1 / 2 : ℝ) • (Pi.single j (1 : ℝ) : Source48Vector)) v = v j
  rw [FCP.BFSSS1V38.source48_polar_eq_two_dot]
  rw [smul_dotProduct]
  have hsingle :
      (Pi.single j (1 : ℝ) : Source48Vector) ⬝ᵥ v = v j := by
    simp [dotProduct, Pi.single_apply]
  rw [hsingle]
  ring

/-- Every original Spin48 element in the genuine source vector
action kernel is killed by EACH original exterior coordinate-dual
contraction, not only a model-space abstract dual. -/
theorem originalSourceSpin48_trivialAction_exteriorCoordinateContractions_zero
    (s : spinGroup Q)
    (hs : ∀ v : Source48Vector,
      FCP.BFSSS1V31.sourceSpin48VectorAction s v = v) :
    ∀ j : Source48Label,
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ Source48Vector))
        (LinearMap.proj j : Module.Dual ℝ Source48Vector)
        ((CliffordAlgebra.equivExterior Q) (s : C)) = 0 := by
  intro j
  rw [← originalSourcePolar_halfSingle_eq_coordinateDual j]
  exact FCP.BFSSS1V52K1D0.originalSourceSpin48_trivialAction_exteriorPolarContractions_zero
    s hs ((1 / 2 : ℝ) • (Pi.single j (1 : ℝ) : Source48Vector))

#print axioms originalSourcePolar_halfSingle_eq_coordinateDual
#print axioms originalSourceSpin48_trivialAction_exteriorCoordinateContractions_zero

end
end FCP.BFSSS1V52K1D1
