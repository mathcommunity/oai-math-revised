import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7KOriginalSourceFlowExactGaugeImplementationProbe

/-!
L6G7L — infinitesimal derivative of the ACTUAL original G4B SU(2)
exterior-Fock fermion action, not a conjectured generator candidate.

The exact source-gauge implementer equality (qualified K, #204)
and the previously qualified original bounded exponential calculus
(G6Z) imply the actual G4B gauge action has derivative J_F(c)
at zero, and a full all-time derivative law along the source-defined
native +i SU(2) curve. Both are vector-valued differentiability
statements on the literal 24-mode Fermion 2 Hilbert space.

No identification with bosonic Gauss operators is asserted.
No Hamiltonian spectral statement follows from this derivative.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace FCP.BFSSSU2PhysicalDomainL6G7L
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G6Z
open FCP.BFSSSU2PhysicalDomainL6G7K

/-- The actual exterior-Fock SU(2) gauge action has precisely the
original source fermion color-current generator as its derivative
on every original Fock vector at the identity. -/
theorem actualGaugeFermion_derivative_zero
    (c : ColorIndex 2) (v : Fermion 2) :
    HasDerivAt
      (fun t : ℝ =>
        fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c t) v)
      (sourceFiberFermionColorGenerator pairedAlgebraData c v)
      0 := by
  have hfun :
      (fun t : ℝ =>
        fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c t) v) =
      (fun t : ℝ => sourceFermionColorFlow c t v) := by
    funext t
    exact (sourceFermionColorFlow_eq_actualGauge_apply c t v).symm
  rw [hfun]
  exact sourceFermionColorFlow_derivative_zero c v

/-- The same genuinely constructed G4B gauge representation is
differentiable at every time along the native source SU(2) curve;
its derivative is the gauge action applied to the literal source
bounded generator on the input state, with source sign preserved. -/
theorem actualGaugeFermion_derivative_all_time
    (c : ColorIndex 2) (t : ℝ) (v : Fermion 2) :
    HasDerivAt
      (fun s : ℝ =>
        fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c s) v)
      (fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c t)
        (sourceFiberFermionColorGenerator pairedAlgebraData c v))
      t := by
  have hfun :
      (fun s : ℝ =>
        fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c s) v) =
      (fun s : ℝ => sourceFermionColorFlow c s v) := by
    funext s
    exact (sourceFermionColorFlow_eq_actualGauge_apply c s v).symm
  have hderiv :
      HasDerivAt
        (fun s : ℝ =>
          fermionGaugeLinearEquiv (sourcePlusIGaugeCurve c s) v)
        (sourceFermionColorFlow c t
          (sourceFiberFermionColorGenerator pairedAlgebraData c v))
        t := by
    rw [hfun]
    exact sourceFermionColorFlow_derivative c t v
  rw [← sourceFermionColorFlow_eq_actualGauge_apply c t
    (sourceFiberFermionColorGenerator pairedAlgebraData c v)]
  exact hderiv

#print axioms actualGaugeFermion_derivative_zero
#print axioms actualGaugeFermion_derivative_all_time
#check @actualGaugeFermion_derivative_zero
#check @actualGaugeFermion_derivative_all_time

end
end FCP.BFSSSU2PhysicalDomainL6G7L
