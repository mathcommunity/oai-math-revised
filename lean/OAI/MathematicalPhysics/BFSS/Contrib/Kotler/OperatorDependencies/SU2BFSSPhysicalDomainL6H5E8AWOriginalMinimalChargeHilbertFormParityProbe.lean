import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8AVOriginalMinimalChargeOperatorActionParityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8ATOriginalPiLp16OutputParityUnitaryProbe
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# H5E8AW — source-original closed sixteen-charge Hilbert FORM under parity

Use the strictly qualified AU true original closed LinearPMap and AV
operator-value parity on its NATURAL domain, with the independently
qualified AT true PiLp 2 Hilbert-output complex unitary.

This proves the EXACT polarized, complex sesquilinear 1/16 source
charge form (not just its diagonal energy), with its actual finite
Hilbert sum output. No invented Hamiltonian, changed normalization,
maximal differential domain, historic Gate93 cache, or manuscript
representation equivalence. The physical-input rebasing and the
associated natural-domain self-adjoint Hamiltonian remain OPEN.
-/

set_option autoImplicit false
set_option maxHeartbeats 240000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8AW
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AD
open FCP.BFSSSU2PhysicalDomainL6H5E8AN
open FCP.BFSSSU2PhysicalDomainL6H5E8AI
open FCP.BFSSSU2PhysicalDomainL6H5E8AT
open FCP.BFSSSU2PhysicalDomainL6H5E8AU
open FCP.BFSSSU2PhysicalDomainL6H5E8AV
open scoped InnerProductSpace

/-- Actual sixteen-component Hilbert output of the TRUE original
source minimal-closed charge LinearPMap on its exact natural domain.
Finite PiLp 2 is the Hilbert direct sum, not the source product norm. -/
noncomputable def originalMinimalChargeHilbertOutput {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (u : (originalMinimalClosedChargeColumn M G).domain) :
    PiLp 2 (fun _ : SpinIndex => FullL2 N) :=
  WithLp.toLp 2 (originalMinimalClosedChargeColumn M G u)

/-- The source charge operator's actual Hilbert output conjugates by
the accepted AT componentwise complex unitary, at every point of
its natural minimal closed domain. -/
theorem originalMinimalChargeHilbertOutput_parity {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (u : (originalMinimalClosedChargeColumn M G).domain) :
    originalMinimalChargeHilbertOutput
      (oppositeGamma M) (originalOppositeGammaGaugeData M G)
      (originalMinimalChargeDomainParityMap M G u) =
    originalChargeHilbertOutputParityUnitary
      (originalMinimalChargeHilbertOutput M G u) := by
  apply PiLp.ext
  intro α
  change
    (originalMinimalClosedChargeColumn (oppositeGamma M)
      (originalOppositeGammaGaugeData M G)
      (originalMinimalChargeDomainParityMap M G u)) α =
    originalChargeHilbertOutputParityUnitary
      (originalMinimalChargeHilbertOutput M G u) α
  rw [originalChargeHilbertOutputParityUnitary_apply]
  exact congrArg (fun ys : SpinIndex → FullL2 N => ys α)
    (originalMinimalChargeOperator_action_parity M G u)

/-- On the genuine sixteen-charge Hilbert direct sum, source
operator-value parity preserves the complex INNER PRODUCT, not only
the norm; this is a true polarized form interface. -/
theorem originalMinimalChargeHilbertInner_parity {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (u v : (originalMinimalClosedChargeColumn M G).domain) :
    inner ℂ
      (originalMinimalChargeHilbertOutput
        (oppositeGamma M) (originalOppositeGammaGaugeData M G)
        (originalMinimalChargeDomainParityMap M G u))
      (originalMinimalChargeHilbertOutput
        (oppositeGamma M) (originalOppositeGammaGaugeData M G)
        (originalMinimalChargeDomainParityMap M G v)) =
    inner ℂ (originalMinimalChargeHilbertOutput M G u)
      (originalMinimalChargeHilbertOutput M G v) := by
  rw [originalMinimalChargeHilbertOutput_parity M G u,
    originalMinimalChargeHilbertOutput_parity M G v]
  exact (originalChargeHilbertOutputParityUnitary (N := N)).inner_map_map
    (originalMinimalChargeHilbertOutput M G u)
    (originalMinimalChargeHilbertOutput M G v)

/-- The EXACT 1/16 complex sesquilinear charge form defined from the
actual original minimal closed charge operator, on its natural domain. -/
noncomputable def originalMinimalChargeClosedForm {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (u v : (originalMinimalClosedChargeColumn M G).domain) : ℂ :=
  (1 / 16 : ℂ) *
    inner ℂ (originalMinimalChargeHilbertOutput M G u)
      (originalMinimalChargeHilbertOutput M G v)

/-- Exact 1/16 NORMALIZED POLARIZED closed-charge form is invariant
under source spatial parity between the valid original and opposite
gamma presentations. No quadratic-form polarization assumption. -/
theorem originalMinimalChargeClosedForm_parity {N : ℕ}
    (M : AlgebraData N) (G : M.GaugeData)
    (u v : (originalMinimalClosedChargeColumn M G).domain) :
    originalMinimalChargeClosedForm
        (oppositeGamma M) (originalOppositeGammaGaugeData M G)
        (originalMinimalChargeDomainParityMap M G u)
        (originalMinimalChargeDomainParityMap M G v) =
      originalMinimalChargeClosedForm M G u v := by
  unfold originalMinimalChargeClosedForm
  rw [originalMinimalChargeHilbertInner_parity M G u v]

#print axioms originalMinimalChargeHilbertOutput
#print axioms originalMinimalChargeHilbertOutput_parity
#print axioms originalMinimalChargeHilbertInner_parity
#print axioms originalMinimalChargeClosedForm
#print axioms originalMinimalChargeClosedForm_parity

end
end FCP.BFSSSU2PhysicalDomainL6H5E8AW
