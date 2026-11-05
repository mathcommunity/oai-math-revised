import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4FRealColorAnnihilatorForwardProbe

/-!
# BFSS SU(2) G4-G — true 24-mode Majorana covariance on Fermion 2

The G4-C creator law and G4-F forward annihilator law have
identical real SU(2) adjoint-color column coefficients U(g) j i.
This stage derives covariance of the *actual* accepted normalized
real/imaginary Majoranas, rather than introducing a new theta model.

The exact 48 spin/color labeling and pinned GaugeData.fermion_adjoint
are subsequent obligations. This file proves all twenty-four
real and all twenty-four imaginary mode identities pointwise.
-/

namespace FCP.BFSSSU2GaugeG4G
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open FCP.BFSSFermionF1 FCP.BFSSFermionF2
open FCP.BFSSSU2GaugeG3C
open FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2GaugeG4C
open FCP.BFSSSU2GaugeG4F

private abbrev s : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

/-- Linear combinations of the exact creator and annihilator
transform with the *same* genuine real forward color coefficients. -/
theorem creator_annihilator_combination_covariant
    (g : GaugeGroup 2) (i : Fin 24) (v : Fermion 2)
    (a b : ℂ) :
    fermionGaugeLinearEquiv g
      (a • creator i v + b • annihilator i v) =
    ∑ j : Fin 24, complexOneParticleMatrix g j i •
      (a • creator j (fermionGaugeLinearEquiv g v) +
       b • annihilator j (fermionGaugeLinearEquiv g v)) := by
  rw [map_add, map_smul, map_smul,
    creator_fermionGauge_covariant,
    annihilator_fermionGauge_forward]
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_add, smul_smul]
  rw [mul_comm a (complexOneParticleMatrix g j i),
      mul_comm b (complexOneParticleMatrix g j i)]

/-- The actual normalized first Majorana equals an explicitly
normalized complex-linear combination on every BFSS state. -/
theorem majorana0_linear_apply (i : Fin 24) (v : Fermion 2) :
    majorana0 i v = s • creator i v + s • annihilator i v := by
  change s • (creator i v + annihilator i v) =
    s • creator i v + s • annihilator i v
  exact smul_add _ _ _

/-- Reproduce the accepted G1-B real/imaginary phase calculation:
the second Majorana is i times creator minus annihilator. -/
private theorem majorana1_phase (i : Fin 24) :
    majorana1 i = s • ((Complex.I : ℂ) • (creator i - annihilator i)) := by
  unfold majorana1
  simp only [star_smul, Complex.star_def, Complex.conj_I, creator_adjoint]
  rw [smul_sub, sub_eq_add_neg]
  ext x
  simp

/-- Exact second Majorana phase, evaluated on the true Fermion 2
Hilbert space, with no false complex conjugation convention. -/
theorem majorana1_linear_apply (i : Fin 24) (v : Fermion 2) :
    majorana1 i v =
      (s * Complex.I) • creator i v +
        (-(s * Complex.I)) • annihilator i v := by
  rw [majorana1_phase]
  change s • ((Complex.I : ℂ) • (creator i v - annihilator i v)) =
    (s * Complex.I) • creator i v +
      (-(s * Complex.I)) • annihilator i v
  rw [smul_smul, smul_sub, sub_eq_add_neg, neg_smul]

/-- Forward gauge covariance of the *actual* first (real)
self-adjoint Majorana operator, for all 24 modes and all states. -/
theorem majorana0_fermionGauge_covariant
    (g : GaugeGroup 2) (i : Fin 24) (v : Fermion 2) :
    fermionGaugeLinearEquiv g (majorana0 i v) =
      ∑ j : Fin 24, complexOneParticleMatrix g j i •
        majorana0 j (fermionGaugeLinearEquiv g v) := by
  rw [majorana0_linear_apply i v]
  simp_rw [majorana0_linear_apply]
  exact creator_annihilator_combination_covariant g i v s s

/-- Forward gauge covariance of the *actual* second (imaginary)
self-adjoint Majorana operator, with its correct phase for all modes. -/
theorem majorana1_fermionGauge_covariant
    (g : GaugeGroup 2) (i : Fin 24) (v : Fermion 2) :
    fermionGaugeLinearEquiv g (majorana1 i v) =
      ∑ j : Fin 24, complexOneParticleMatrix g j i •
        majorana1 j (fermionGaugeLinearEquiv g v) := by
  rw [majorana1_linear_apply i v]
  simp_rw [majorana1_linear_apply]
  exact creator_annihilator_combination_covariant g i v
    (s * Complex.I) (-(s * Complex.I))

#print axioms creator_annihilator_combination_covariant
#print axioms majorana0_linear_apply
#print axioms majorana1_phase
#print axioms majorana1_linear_apply
#print axioms majorana0_fermionGauge_covariant
#print axioms majorana1_fermionGauge_covariant

end
end FCP.BFSSSU2GaugeG4G
