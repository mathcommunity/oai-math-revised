import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7DRotatedThetaOperatorDerivativeProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6LOriginalInfinitesimalColorActionProbe

/-!
L6G7E — the literal original bounded Majorana combination B_A(t)
obeys B'_A(t) = [J_F(c), B_A(t)] at EVERY real time.

Only accepted native source results are imported:
* L6G6L — exact original generator commutator on theta;
* L6G7C/D — native SU(2) all-time color derivative and the
  differentiated source bounded theta sum.
A linear-map finite-color transport identity performs the sum algebra
and real-to-complex scalar conversion in an abstract module BEFORE
instantiation with the 2^24-dimensional original Fock fiber.
The unqualified pointwise L6G7A wrapper is not used.

This is an operator-valued evolution identity, not yet integrated
finite-time source gauge covariance, original G4B action equality,
combined Gauss constraint or a spectral theorem.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace FCP.BFSSSU2PhysicalDomainL6G7E
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6L
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7D

/-! Keep the finite-sum commutator calculation separate from every
concrete Fock instance and every particular Pauli/gamma definition. -/
private theorem abstract_finite_color_commutator
    {R C : Type*} [Ring R] [Algebra ℂ R] [Fintype C]
    (J : R) (theta : C → R) (F : C → C → ℂ)
    (r : C → ℂ)
    (hcomm : ∀ d, J * theta d - theta d * J =
      ∑ b : C, F b d • theta b) :
    J * (∑ d : C, r d • theta d) -
      (∑ d : C, r d • theta d) * J =
      ∑ b : C, (∑ d : C, F b d * r d) • theta b := by
  classical
  calc
    _ = ∑ d : C, r d • (J * theta d - theta d * J) := by
      simp only [Finset.mul_sum, Finset.sum_mul,
        mul_smul_comm, smul_mul_assoc,
        ← Finset.sum_sub_distrib, ← smul_sub]
    _ = ∑ d : C, ∑ b : C, (r d * F b d) • theta b := by
      simp_rw [hcomm, Finset.smul_sum, smul_smul]
    _ = ∑ b : C, ∑ d : C, (F b d * r d) • theta b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      rw [mul_comm (r d) (F b d)]
    _ = ∑ b : C, (∑ d : C, F b d * r d) • theta b := by
      simp only [Finset.sum_smul]

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

/-- The exact ORIGINAL color current has output B/input D commutator
coefficients matching the independently qualified source color ODE.
The sign follows L6G6L and the proved antisymmetry, not a new choice. -/
theorem sourceGenerator_theta_comm_output
    (c : ColorIndex 2) (spin : SpinIndex) (d : ColorIndex 2) :
    sourceFiberFermionColorGenerator pairedAlgebraData c *
        pairedAlgebraData.theta spin d -
      pairedAlgebraData.theta spin d *
        sourceFiberFermionColorGenerator pairedAlgebraData c =
      ∑ b : ColorIndex 2,
        (pairedAlgebraData.structureConstant b d c : ℂ) •
          pairedAlgebraData.theta spin b := by
  have hcomm :=
    sourceFiberFermionColorGenerator_comm pairedAlgebraData
      sourceNormalizedPauliColor c spin d
  have hskew (b : ColorIndex 2) :
      (pairedAlgebraData.structureConstant b d c : ℂ) =
        -(pairedAlgebraData.structureConstant d b c : ℂ) := by
    simpa only [Complex.ofReal_neg] using
      congrArg (fun z : ℝ => (z : ℂ))
        (FCP.BFSSSU2PhysicalDomainL6G6D.sourceSU2StructureConstant_swapFirst
          pairedAlgebraData sourceNormalizedPauliColor d b c)
  calc
    _ = -(∑ b : ColorIndex 2,
          (pairedAlgebraData.structureConstant d b c : ℂ) •
            pairedAlgebraData.theta spin b) := hcomm
    _ = ∑ b : ColorIndex 2,
          -((pairedAlgebraData.structureConstant d b c : ℂ) •
            pairedAlgebraData.theta spin b) := by simp only [Finset.sum_neg_distrib]
    _ = ∑ b : ColorIndex 2,
          (pairedAlgebraData.structureConstant b d c : ℂ) •
            pairedAlgebraData.theta spin b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [hskew b]
      exact (neg_smul _ _).symm

/-! Independent Issue #26 strategy: transport a finite coefficient vector
through a linear map. All scalar casts and sum rearrangements are proved
with an abstract module, before the original Fock operators are supplied.
Continuity is unnecessary here: L6G7D already proves the derivative. -/
private theorem linear_finite_color_transport
    {V C : Type*} [AddCommGroup V] [Module ℂ V] [Fintype C]
    (L : V →ₗ[ℂ] V) (theta : C → V)
    (F : C → C → ℝ) (r : C → ℝ)
    (h : ∀ d, L (theta d) = ∑ b : C, (F b d : ℂ) • theta b) :
    L (∑ d : C, (r d : ℂ) • theta d) =
      ∑ b : C, ((∑ d : C, F b d * r d : ℝ) : ℂ) • theta b := by
  classical
  calc
    _ = ∑ d : C, (r d : ℂ) • L (theta d) := by
      simp only [map_sum, map_smul]
    _ = ∑ d : C, ∑ b : C, ((r d : ℂ) * (F b d : ℂ)) • theta b := by
      simp_rw [h, Finset.smul_sum, smul_smul]
    _ = ∑ b : C, ∑ d : C, ((F b d : ℂ) * (r d : ℂ)) • theta b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      rw [mul_comm (r d : ℂ) (F b d : ℂ)]
    _ = _ := by
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_smul]

/-- The commutator as a linear map on the EXACT source operator space.
Its arguments are arbitrary operators; no concrete Majorana is expanded. -/
private def sourceCommutator (J : SourceFiberEnd) :
    SourceFiberEnd →ₗ[ℂ] SourceFiberEnd where
  toFun T := J * T - T * J
  map_add' S T := by
    simp only [mul_add, add_mul]
    abel
  map_smul' z T := by
    simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, smul_sub]

-- Restrict elaborator transparency only inside this file. These constants
-- retain their definitions in the kernel. Their accepted source files,
-- values and theorem statements are unchanged. No recursion limit is raised.
attribute [local irreducible] pairedAlgebraData sourceFiberFermionColorGenerator

/-- Small, rigidly typed source bridge into the linear-map interface. -/
private theorem sourceCommutator_theta
    (c : ColorIndex 2) (spin : SpinIndex) (d : ColorIndex 2) :
    sourceCommutator (sourceFiberFermionColorGenerator pairedAlgebraData c)
        (pairedAlgebraData.theta spin d) =
      ∑ b : ColorIndex 2,
        (pairedAlgebraData.structureConstant b d c : ℂ) •
          pairedAlgebraData.theta spin b := by
  change sourceFiberFermionColorGenerator pairedAlgebraData c *
      pairedAlgebraData.theta spin d - pairedAlgebraData.theta spin d *
      sourceFiberFermionColorGenerator pairedAlgebraData c = _
  exact sourceGenerator_theta_comm_output c spin d

/-- ACTUAL original bounded source theta combination evolves by
the ORIGINAL skew fermion generator, for every time and theta index. -/
theorem sourceRotatedTheta_comm_evolution
    (c : ColorIndex 2) (spin : SpinIndex)
    (A : ColorIndex 2) (t : ℝ) :
    sourceFiberFermionColorGenerator pairedAlgebraData c *
        sourceRotatedTheta c spin A t -
      sourceRotatedTheta c spin A t *
        sourceFiberFermionColorGenerator pairedAlgebraData c =
      sourceRotatedThetaDerivative c spin A t := by
  change sourceCommutator (sourceFiberFermionColorGenerator pairedAlgebraData c)
      (sourceRotatedTheta c spin A t) = sourceRotatedThetaDerivative c spin A t
  unfold sourceRotatedTheta sourceRotatedThetaDerivative
  exact linear_finite_color_transport
    (sourceCommutator (sourceFiberFermionColorGenerator pairedAlgebraData c))
    (pairedAlgebraData.theta spin)
    (fun b d => pairedAlgebraData.structureConstant b d c)
    (fun d => pairedAlgebraData.adjointCoefficient (sourcePlusIGaugeCurve c t) A d)
    (sourceCommutator_theta c spin)

/-- The all-time original 48-theta source operator evolution equation.
No unverified Fock-vector transport or finite-time identification is used. -/
theorem sourceRotatedTheta_deriv_comm_all
    (c : ColorIndex 2) (spin : SpinIndex)
    (A : ColorIndex 2) (t : ℝ) :
    HasDerivAt (fun u : ℝ => sourceRotatedTheta c spin A u)
      (sourceFiberFermionColorGenerator pairedAlgebraData c *
          sourceRotatedTheta c spin A t -
        sourceRotatedTheta c spin A t *
          sourceFiberFermionColorGenerator pairedAlgebraData c) t := by
  rw [sourceRotatedTheta_comm_evolution c spin A t]
  exact sourceRotatedTheta_deriv_all c spin A t

#print axioms linear_finite_color_transport
#print axioms sourceCommutator
#print axioms sourceCommutator_theta
#print axioms abstract_finite_color_commutator
#print axioms sourceGenerator_theta_comm_output
#print axioms sourceRotatedTheta_comm_evolution
#print axioms sourceRotatedTheta_deriv_comm_all
#check @sourceRotatedTheta_deriv_comm_all

end
end FCP.BFSSSU2PhysicalDomainL6G7E
