import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H3CActualOriginalFullL2GaugeCoreInnerContinuityProbe

/-!
L6H4A — source EXACT FullL2 BFSS SU(2) orbital distance-squared
identity and its continuity.

Build on the two independently source-qualified components:
L6G7W actual Original FullL2 SU2 isometry (#227),
L6H3C true Original FullL2 Hilbert matrix-coefficient
continuity for smooth-core vectors (#247).

No re-elaboration of the long original Fock operator, no proxy
Hilbert space, no new hypothesis. This is the scalar real
polarization bridge; strong norm-topology continuity itself
is deliberately reserved for separately compiled L6H4B.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H4A
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6G7W
open FCP.BFSSSU2PhysicalDomainL6H3C
open MeasureTheory

/-- The exact original BFSS source full-L² gauge orbit has
real Hilbert polarization with both norm terms equal to the
UNCHANGED original core vector's norm. -/
theorem actualOriginalFullL2GaugeCore_distSq_eq_inner
    (f : SmoothCore 2) (g h : GaugeGroup 2) :
    ‖actualOriginalFullL2GaugePairCLM g (coreToL2 f) -
      actualOriginalFullL2GaugePairCLM h (coreToL2 f)‖ ^ 2 =
    ‖coreToL2 f‖ ^ 2 -
      2 * Complex.re
        (inner ℂ (actualOriginalFullL2GaugePairCLM g (coreToL2 f))
          (actualOriginalFullL2GaugePairCLM h (coreToL2 f))) +
      ‖coreToL2 f‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), actualOriginalFullL2GaugePair_norm g,
    actualOriginalFullL2GaugePair_norm h]
  simp only [RCLike.re_to_complex]

/-- Genuine source BFSS orbit distance SQUARED varies
continuously with the original SU(2) gauge parameter. This
does not yet assert that the FullL2-valued orbit is continuous. -/
theorem actualOriginalFullL2GaugeCore_distSq_continuous
    (f : SmoothCore 2) (h : GaugeGroup 2) :
    Continuous (fun g : GaugeGroup 2 =>
      ‖actualOriginalFullL2GaugePairCLM g (coreToL2 f) -
        actualOriginalFullL2GaugePairCLM h (coreToL2 f)‖ ^ 2) := by
  have hcoef :
      Continuous (fun g : GaugeGroup 2 =>
        Complex.re (inner ℂ
          (actualOriginalFullL2GaugePairCLM g (coreToL2 f))
          (actualOriginalFullL2GaugePairCLM h (coreToL2 f)))) :=
    Complex.continuous_re.comp
      (actualOriginalFullL2GaugeCore_innerContinuous f h)
  have hc :
      Continuous (fun g : GaugeGroup 2 =>
        ‖coreToL2 f‖ ^ 2 -
          2 * Complex.re (inner ℂ
            (actualOriginalFullL2GaugePairCLM g (coreToL2 f))
            (actualOriginalFullL2GaugePairCLM h (coreToL2 f))) +
          ‖coreToL2 f‖ ^ 2) :=
    (continuous_const.sub (continuous_const.mul hcoef)).add continuous_const
  have heq :
      (fun g : GaugeGroup 2 =>
        ‖actualOriginalFullL2GaugePairCLM g (coreToL2 f) -
          actualOriginalFullL2GaugePairCLM h (coreToL2 f)‖ ^ 2) =
      (fun g : GaugeGroup 2 =>
        ‖coreToL2 f‖ ^ 2 -
          2 * Complex.re (inner ℂ
            (actualOriginalFullL2GaugePairCLM g (coreToL2 f))
            (actualOriginalFullL2GaugePairCLM h (coreToL2 f))) +
          ‖coreToL2 f‖ ^ 2) := by
    funext g
    exact actualOriginalFullL2GaugeCore_distSq_eq_inner f g h
  rw [heq]
  exact hc

#print axioms actualOriginalFullL2GaugeCore_distSq_eq_inner
#print axioms actualOriginalFullL2GaugeCore_distSq_continuous
#check @actualOriginalFullL2GaugeCore_distSq_continuous

end
end FCP.BFSSSU2PhysicalDomainL6H4A
