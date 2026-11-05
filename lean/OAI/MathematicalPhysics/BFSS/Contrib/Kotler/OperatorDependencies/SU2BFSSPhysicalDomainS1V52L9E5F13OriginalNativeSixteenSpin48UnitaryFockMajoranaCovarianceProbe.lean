import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5F12OriginalNativeSixteenSpin48CliffordStarFockAdjointProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L9E5D1OriginalNativeSpin48FockCliffordAlgebraicCovarianceProbe

/-!
S1V52L9E5F13 — STAGED ONLY / NOT KERNEL QUALIFIED, NO CI.

The actual ORIGINAL SU2 GaugeGroup 2 → native ordered sixteen-block
Spin48 map induces unitary Fock operators (F11 verified).
The new F12 source-exact star/adjoint theorem (PENDING STRICT CI)
will identify the right Clifford-star image factor in the
existing original-source algebraic Fock covariance L9E5D1 with
the true Hilbert adjoint of the native Fock operator.

This produces exact Hilbert-operator covariance on ALL original
48-real source Majorana generators. It makes no assumption
that rho is globally star-compatible on odd Cliffords.
The separate original physical gauge implementation, potential
central character ambiguity, continuity and BFSS spectral gap
remain unproved and are NOT identified here.

Prerequisite source L9E5D1 must itself compile source-exact and
pass the strict allowed-axiom audit in the F13 workflow; do NOT
count it merely because an older source file exists.
-/

set_option autoImplicit false
set_option maxHeartbeats 360000

namespace FCP.BFSSS1V52L9E5F13
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L8E
open FCP.BFSSS1V52L9E4
open FCP.BFSSS1V52L9E5C1
open FCP.BFSSS1V52L9E5D1
open FCP.BFSSS1V52L9E5F12
open FCP.BFSSSU2PhysicalDomainS1J

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Actual native original SU2-to-Spin48 sixteen-block Fock image
conjugates the genuine original Fermion2 Majorana operator by
its HILBERT ADJOINT (not merely rho of source Clifford star)
with exactly the pinned original source gauge matrix action. -/
theorem originalNativeSixteenSpinFock_unitary_majorana_covariance
    (g : GaugeGroup 2) (v : Source48Vector) :
    originalFockCliffordAlgHom
        (((originalNativeSixteenSpinHom g : spinGroup Q) : C)) *
      originalFockGammaRealLinear v *
      star (originalFockCliffordAlgHom
        (((originalNativeSixteenSpinHom g : spinGroup Q) : C))) =
      originalFockGammaRealLinear
        ((sourceRealMajoranaMatrix g).mulVec v) := by
  have h := originalNativeSpinFock_clifford_generator_covariance g v
  rw [originalNativeSixteenSpin48_star_fock_adjoint g] at h
  exact h

-- Additional dependency audit: these two are imported original
-- algebraic-covariance roots, NOT new F13 declarations. Exact
-- source hash and allowed axioms must be independently visible.
#print axioms FCP.BFSSS1V52L9E5D1.originalFockCliffordAlgHom_conj_generator
#print axioms FCP.BFSSS1V52L9E5D1.originalNativeSpinFock_clifford_generator_covariance
#print axioms originalNativeSixteenSpinFock_unitary_majorana_covariance

end
end FCP.BFSSS1V52L9E5F13
