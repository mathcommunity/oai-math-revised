import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6YOriginalOneParticleDerivativeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6SOriginalGaugeVacuumIdentificationProbe
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.LinearAlgebra.Complex.Module

/-!
L6G6Z — the actual bounded original Fock fermion COLOR generator
has a differentiable unitary one-parameter flow. Its exact common
source/gauge vacuum is fixed for every real time.

Use the norm-convergent bounded exponential calculus already verified
for Fock spin rotations (S3H), and the source's exact K/L/R/S theorems.
The underlying bounded-flow proof pattern is also in pinned
OAI.RepresentationTheory.VertexAlgebra.BoundedFlows.

Scientific boundary: this proves NO finite-time covariance with the
genuine G4B gauge action. S1B may be applied only after that separate
same-48-Majorana covariance premise is discharged. This module neither
identifies the gauge generator nor proves combined Gauss or spectrum.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace FCP.BFSSSU2PhysicalDomainL6G6Z
noncomputable section

open scoped Topology
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6S

private abbrev SourceFiberEnd := Fermion 2 →L[ℂ] Fermion 2

local instance sourceFockRationalNormedAlgebra :
    NormedAlgebra ℚ SourceFiberEnd :=
  .restrictScalars ℚ ℂ SourceFiberEnd

private theorem sourceNormalizedPauliColor :
    ∀ a : ColorIndex 2,
      pairedAlgebraData.color a = FCP.BFSSSU2.normalizedPauli a := by
  intro a
  calc
    pairedAlgebraData.color a =
        FCP.BFSSSU2Full.concreteAlgebraData.color a :=
      pairedAlgebraData_color a
    _ = FCP.BFSSSU2.normalizedPauli a :=
      FCP.BFSSSU2Full.concreteAlgebraData_color a

/-- Exact source J_F = i G_F is skew-adjoint on Fermion 2. -/
theorem sourceFermionColorGenerator_skew (c : ColorIndex 2) :
    sourceFiberFermionColorGenerator pairedAlgebraData c ∈
      skewAdjoint SourceFiberEnd := by
  rw [skewAdjoint.mem_iff]
  exact sourceFiberFermionColorGenerator_star_eq_neg
    pairedAlgebraData sourceNormalizedPauliColor c

/-- Norm-convergent flow of the LITERAL source bounded color generator. -/
noncomputable def sourceFermionColorFlow
    (c : ColorIndex 2) (t : ℝ) : SourceFiberEnd :=
  NormedSpace.exp (t • sourceFiberFermionColorGenerator pairedAlgebraData c)

/-- Unitarity of the actual bounded source color-current exponential. -/
theorem sourceFermionColorFlow_unitary
    (c : ColorIndex 2) (t : ℝ) :
    sourceFermionColorFlow c t ∈ unitary SourceFiberEnd := by
  unfold sourceFermionColorFlow
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star (((t : ℂ) • sourceFiberFermionColorGenerator pairedAlgebraData c)) =
    -(((t : ℂ) • sourceFiberFermionColorGenerator pairedAlgebraData c))
  have hstar : star (t : ℂ) = (t : ℂ) := by
    rw [RCLike.star_def]
    exact RCLike.conj_ofReal t
  rw [star_smul, hstar,
    skewAdjoint.mem_iff.mp (sourceFermionColorGenerator_skew c), smul_neg]

theorem sourceFermionColorFlow_zero (c : ColorIndex 2) :
    sourceFermionColorFlow c 0 = 1 := by
  change NormedSpace.exp ((0 : ℂ) •
    sourceFiberFermionColorGenerator pairedAlgebraData c) = 1
  have hzero :
      (0 : ℂ) • sourceFiberFermionColorGenerator pairedAlgebraData c =
        (0 : SourceFiberEnd) := by
    ext v
    simp
  rw [hzero, NormedSpace.exp_zero]

theorem sourceFermionColorFlow_add
    (c : ColorIndex 2) (s t : ℝ) :
    sourceFermionColorFlow c (s+t) =
      sourceFermionColorFlow c s * sourceFermionColorFlow c t := by
  change NormedSpace.exp (((s+t : ℝ) : ℂ) •
      sourceFiberFermionColorGenerator pairedAlgebraData c) =
    NormedSpace.exp ((s : ℂ) •
      sourceFiberFermionColorGenerator pairedAlgebraData c) *
    NormedSpace.exp ((t : ℂ) •
      sourceFiberFermionColorGenerator pairedAlgebraData c)
  have hadd :
      (((s : ℝ) : ℂ) + ((t : ℝ) : ℂ)) •
          sourceFiberFermionColorGenerator pairedAlgebraData c =
        (((s : ℝ) : ℂ) • sourceFiberFermionColorGenerator pairedAlgebraData c) +
          (((t : ℝ) : ℂ) • sourceFiberFermionColorGenerator pairedAlgebraData c) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [_root_.add_apply, _root_.smul_apply]
    exact add_smul (s : ℂ) (t : ℂ)
      (sourceFiberFermionColorGenerator pairedAlgebraData c v)
  rw [Complex.ofReal_add, hadd]
  exact NormedSpace.exp_add_of_commute
    (((Commute.refl
      (sourceFiberFermionColorGenerator pairedAlgebraData c)).smul_left (s : ℂ)).smul_right (t : ℂ))

theorem sourceFermionColorFlow_norm
    (c : ColorIndex 2) (t : ℝ) (v : Fermion 2) :
    ‖sourceFermionColorFlow c t v‖ = ‖v‖ := by
  exact ContinuousLinearMap.norm_map_of_mem_unitary
    (sourceFermionColorFlow_unitary c t) v

/-- Real-time derivative of the actual bounded source color flow. -/
theorem sourceFermionColorFlow_derivative
    (c : ColorIndex 2) (t : ℝ) (v : Fermion 2) :
    HasDerivAt (fun s : ℝ => sourceFermionColorFlow c s v)
      (sourceFermionColorFlow c t
        (sourceFiberFermionColorGenerator pairedAlgebraData c v)) t := by
  change HasDerivAt
    (fun s : ℝ =>
      (NormedSpace.exp (s • sourceFiberFermionColorGenerator pairedAlgebraData c)) v)
    ((NormedSpace.exp (t • sourceFiberFermionColorGenerator pairedAlgebraData c))
      (sourceFiberFermionColorGenerator pairedAlgebraData c v)) t
  exact ((ContinuousLinearMap.apply ℂ (Fermion 2) v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const
      (sourceFiberFermionColorGenerator pairedAlgebraData c) t)

theorem sourceFermionColorFlow_derivative_zero
    (c : ColorIndex 2) (v : Fermion 2) :
    HasDerivAt (fun t : ℝ => sourceFermionColorFlow c t v)
      (sourceFiberFermionColorGenerator pairedAlgebraData c v) 0 := by
  simpa only [sourceFermionColorFlow_zero, one_apply_eq_self] using
    sourceFermionColorFlow_derivative c 0 v

/-- The generator and its unitary flow give a measured Lipschitz bound. -/
theorem sourceFermionColorFlow_time_bound
    (c : ColorIndex 2) (s t : ℝ) (v : Fermion 2) :
    ‖sourceFermionColorFlow c t v - sourceFermionColorFlow c s v‖ ≤
      ‖sourceFiberFermionColorGenerator pairedAlgebraData c v‖ * |t-s| := by
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ => sourceFermionColorFlow c u v)
    (f' := fun u : ℝ =>
      sourceFermionColorFlow c u
        (sourceFiberFermionColorGenerator pairedAlgebraData c v))
    (s := Set.univ) (x := s) (y := t)
    (fun u _ => (sourceFermionColorFlow_derivative c u v).hasDerivWithinAt)
    (fun u _ =>
      (sourceFermionColorFlow_norm c u
        (sourceFiberFermionColorGenerator pairedAlgebraData c v)).le)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa only [Real.norm_eq_abs] using hb

theorem sourceFermionColorFlow_initial_bound
    (c : ColorIndex 2) (t : ℝ) (v : Fermion 2) :
    ‖sourceFermionColorFlow c t v - v‖ ≤
      |t| * ‖sourceFiberFermionColorGenerator pairedAlgebraData c v‖ := by
  simpa only [sourceFermionColorFlow_zero, one_apply_eq_self,
    sub_zero, mul_comm] using
    sourceFermionColorFlow_time_bound c 0 t v

/-- Both the bounded flow and the actual exterior gauge action
fix the SAME nonzero source Fock vacuum; no gauge equality assumed. -/
theorem sourceFermionColorFlow_vacuum
    (c : ColorIndex 2) (t : ℝ) :
    sourceFermionColorFlow c t fermionVacuum = fermionVacuum := by
  have hb := sourceFermionColorFlow_initial_bound c t fermionVacuum
  rw [sourcePairedFermionColorGenerator_actualGaugeVacuum c,
    norm_zero, mul_zero] at hb
  have hz :
      ‖sourceFermionColorFlow c t fermionVacuum - fermionVacuum‖ = 0 :=
    le_antisymm hb (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

#print axioms sourceFermionColorGenerator_skew
#print axioms sourceFermionColorFlow_unitary
#print axioms sourceFermionColorFlow_zero
#print axioms sourceFermionColorFlow_add
#print axioms sourceFermionColorFlow_norm
#print axioms sourceFermionColorFlow_derivative
#print axioms sourceFermionColorFlow_derivative_zero
#print axioms sourceFermionColorFlow_time_bound
#print axioms sourceFermionColorFlow_initial_bound
#print axioms sourceFermionColorFlow_vacuum
#check @sourceFermionColorFlow_derivative_zero
#check @sourceFermionColorFlow_vacuum

end
end FCP.BFSSSU2PhysicalDomainL6G6Z
