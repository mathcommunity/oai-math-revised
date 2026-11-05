import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6EOriginalSpinorBilinearResponseProbe

/-!
L6G6F — ACTUAL original source spinor-bilinear commutator coefficient
to the signed gamma/gammaTwo Fierz kernel.

The source -i kinetic weight, source 1/2 quadratic weight, two
derivative legs, original Pauli structure constants and original
real spinor rows are all preserved. Before specializing to BFSS
we prove the color selector and antisymmetric coefficient identity
as a finite complex scalar statement.

This is a literal fixed-fermion-label coefficient identity, not
yet the Gauss decomposition or ordered Majorana operator identity.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G6F
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G4B
open FCP.BFSSSU2PhysicalDomainL6G5B
open FCP.BFSSSU2PhysicalDomainL6G6A
open FCP.BFSSSU2PhysicalDomainL6G6D
open FCP.BFSSSU2PhysicalDomainL6G6E

/-- Genuine original quadratic pair source scalar equals the
original REAL gammaTwo row (with no changed normalization). -/
theorem sourceSpinorQuadraticPairWeight_eq_row
    (M : AlgebraData 2) (w : SpinIndex → ℝ)
    (p : FermionLabel 2) (u t : BosonLabel 2) :
    sourceSpinorQuadraticPairWeight M w p u t =
      (((1 / 2 : ℝ) * M.structureConstant p.2 u.2 t.2 *
        ((w ᵥ* M.gammaTwo u.1 t.1) p.1) : ℝ) : ℂ) := by
  unfold sourceSpinorQuadraticPairWeight sourceQuadraticWeight
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  change (∑ α : SpinIndex,
      w α * ((1 / 2 : ℝ) * M.structureConstant p.2 u.2 t.2 *
        M.gammaTwo u.1 t.1 α p.1)) =
    (1 / 2 : ℝ) * M.structureConstant p.2 u.2 t.2 *
      (∑ α : SpinIndex, w α * M.gammaTwo u.1 t.1 α p.1)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  ring

/-- Original -i kinetic weight with its actual source gamma row. -/
theorem sourceSpinorKineticWeight_eq_sourceRow
    (M : AlgebraData 2) (w : SpinIndex → ℝ)
    (hgamma : M.gamma = originalGamma)
    (p : FermionLabel 2) (u : BosonLabel 2) :
    sourceSpinorKineticWeight M w p u =
      if u.2 = p.2 then
        -Complex.I * ((((w ᵥ* M.gamma u.1) p.1 : ℝ) : ℂ))
      else 0 := by
  simpa only [hgamma] using
    (sourceSpinorKineticWeight_eq M w hgamma p u)

/-- A color selector collapses a finite sum over ORIGINAL paired
bosonic labels, without assumptions about color structure constants. -/
private theorem finiteColorSelectorChannel
    {I C : Type*} [Fintype I] [Fintype C] [DecidableEq C]
    (a : C) (g : I → ℂ)
    (Q : I → C → I → C → ℂ) (x : I → C → ℂ) :
    (∑ u : I × C, ∑ t : I × C,
      (if u.2 = a then g u.1 else 0) *
        Q u.1 u.2 t.1 t.2 * x t.1 t.2) =
      ∑ i : I, ∑ k : I, ∑ c : C,
        g i * Q i a k c * x k c := by
  classical
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ d : C, ∑ k : I, ∑ c : C,
      (if d = a then g i else 0) * Q i d k c * x k c) =
        ∑ k : I, ∑ c : C, ∑ d : C,
          (if d = a then g i else 0) * Q i d k c * x k c := by
            calc
              _ = ∑ k : I, ∑ d : C, ∑ c : C,
                    (if d = a then g i else 0) * Q i d k c * x k c :=
                Finset.sum_comm
              _ = _ := by
                apply Finset.sum_congr rfl
                intro k _
                exact Finset.sum_comm
    _ = ∑ k : I, ∑ c : C, g i * Q i a k c * x k c := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro c _
      have hterm (d : C) :
          (if d = a then g i else 0) * Q i d k c * x k c =
            if d = a then g i * Q i a k c * x k c else 0 := by
        by_cases hd : d = a
        · subst d
          simp
        · simp [hd]
      simp_rw [hterm]
      simp

/-- Universal finite color-skew and gamma-row contraction.
The -i and 1/2 source factors and the factor-two source derivative
are explicitly retained. Source color antisymmetry is a premise,
discharged below by an ACCEPTED original Pauli color theorem. -/
private theorem finiteColorSkewSpinorContraction
    {I C : Type*} [Fintype I] [Fintype C] [DecidableEq C]
    (F : C → C → C → ℂ)
    (hF : ∀ a b c, F b a c = -F a b c)
    (g h : I → ℂ) (U V : I → I → ℂ)
    (x : I → C → ℂ) (a b : C) :
    (2 : ℂ) * (∑ u : I × C, ∑ t : I × C,
      (((if u.2 = a then -Complex.I * g u.1 else 0) *
           ((1 / 2 : ℂ) * F b u.2 t.2 * U u.1 t.1)) -
        ((if u.2 = b then -Complex.I * h u.1 else 0) *
           ((1 / 2 : ℂ) * F a u.2 t.2 * V u.1 t.1))) *
        x t.1 t.2) =
      Complex.I * (∑ i : I, ∑ k : I, ∑ c : C,
        (F a b c * x k c) * (g i * U i k + h i * V i k)) := by
  let A : (I × C) → (I × C) → ℂ := fun u t =>
    (if u.2 = a then -Complex.I * g u.1 else 0) *
      ((1 / 2 : ℂ) * F b u.2 t.2 * U u.1 t.1)
  let B : (I × C) → (I × C) → ℂ := fun u t =>
    (if u.2 = b then -Complex.I * h u.1 else 0) *
      ((1 / 2 : ℂ) * F a u.2 t.2 * V u.1 t.1)
  have ha :
      (∑ u : I × C, ∑ t : I × C, A u t * x t.1 t.2) =
        ∑ i : I, ∑ k : I, ∑ c : C,
          ((-Complex.I * g i) * ((1 / 2 : ℂ) * F b a c * U i k)) * x k c :=
    finiteColorSelectorChannel a (fun i => -Complex.I * g i)
      (fun i d k c => (1 / 2 : ℂ) * F b d c * U i k) x
  have hb :
      (∑ u : I × C, ∑ t : I × C, B u t * x t.1 t.2) =
        ∑ i : I, ∑ k : I, ∑ c : C,
          ((-Complex.I * h i) * ((1 / 2 : ℂ) * F a b c * V i k)) * x k c :=
    finiteColorSelectorChannel b (fun i => -Complex.I * h i)
      (fun i d k c => (1 / 2 : ℂ) * F a d c * V i k) x
  have hpoint (i k : I) (c : C) :
      (2 : ℂ) *
        (((-Complex.I * g i) * ((1 / 2 : ℂ) * F b a c * U i k)) * x k c -
          ((-Complex.I * h i) * ((1 / 2 : ℂ) * F a b c * V i k)) * x k c) =
        Complex.I * ((F a b c * x k c) * (g i * U i k + h i * V i k)) := by
    rw [hF a b c]
    ring
  change (2 : ℂ) *
    (∑ u : I × C, ∑ t : I × C, (A u t - B u t) * x t.1 t.2) = _
  calc
    _ = (2 : ℂ) *
      ((∑ u : I × C, ∑ t : I × C, A u t * x t.1 t.2) -
       (∑ u : I × C, ∑ t : I × C, B u t * x t.1 t.2)) := by
         simp only [sub_mul, Finset.sum_sub_distrib]
    _ = (2 : ℂ) *
      ((∑ i : I, ∑ k : I, ∑ c : C,
          ((-Complex.I * g i) * ((1 / 2 : ℂ) * F b a c * U i k)) * x k c) -
       (∑ i : I, ∑ k : I, ∑ c : C,
          ((-Complex.I * h i) * ((1 / 2 : ℂ) * F a b c * V i k)) * x k c)) := by
            rw [ha, hb]
    _ = ∑ i : I, ∑ k : I, ∑ c : C,
      (2 : ℂ) *
        (((-Complex.I * g i) * ((1 / 2 : ℂ) * F b a c * U i k)) * x k c -
          ((-Complex.I * h i) * ((1 / 2 : ℂ) * F a b c * V i k)) * x k c) := by
            simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
    _ = ∑ i : I, ∑ k : I, ∑ c : C,
      Complex.I * ((F a b c * x k c) * (g i * U i k + h i * V i k)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro c _
        exact hpoint i k c
    _ = _ := by simp only [Finset.mul_sum]

/-- The exact original row-spinor Fierz coefficient, BEFORE applying
the already accepted generalized source Fierz identity. -/
def sourceOriginalFermionRowKernel
    (M : AlgebraData 2) (w : SpinIndex → ℝ)
    (p q : FermionLabel 2) (x : Boson 2) : ℂ :=
  Complex.I * (∑ i : SpaceIndex, ∑ k : SpaceIndex, ∑ c : ColorIndex 2,
    ((M.structureConstant p.2 q.2 c : ℂ) * ((x (k,c) : ℝ) : ℂ)) *
      (((((w ᵥ* M.gamma i) p.1 : ℝ) : ℂ) *
          (((w ᵥ* M.gammaTwo i k) q.1 : ℝ) : ℂ)) +
       ((((w ᵥ* M.gamma i) q.1 : ℝ) : ℂ) *
          (((w ᵥ* M.gammaTwo i k) p.1 : ℝ) : ℂ))))

/-- L6G6E's unchanged original pointwise response is EXACTLY
the original signed gamma/gammaTwo Fierz kernel. In particular,
the relative overall +i comes from the source -i kinetic factor,
the source color skew and BOTH original derivative legs. -/
theorem sourceAllSpinorResponsePoint_eq_originalRowKernel
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (hgamma : M.gamma = originalGamma)
    (w : SpinIndex → ℝ) (p q : FermionLabel 2)
    (x : Boson 2) :
    sourceAllSpinorResponsePoint M w p q x =
      sourceOriginalFermionRowKernel M w p q x := by
  rw [sourceAllSpinorResponsePoint_eq_bilinear M hcolor w p q x]
  unfold sourceOriginalFermionRowKernel
  simp_rw [sourceSpinorKineticWeight_eq_sourceRow M w hgamma,
    sourceSpinorQuadraticPairWeight_eq_row M w]
  have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by
    norm_num
  simp only [Complex.ofReal_mul, hhalf]
  have hf (a b c : ColorIndex 2) :
      (M.structureConstant b a c : ℂ) =
        -(M.structureConstant a b c : ℂ) := by
    simpa only [Complex.ofReal_neg] using congrArg
      (fun t : ℝ => (t : ℂ))
      (sourceSU2StructureConstant_swapFirst M hcolor a b c)
  -- The last step is a reusable scalar finite sum theorem, not
  -- normalization of the concrete source differential operators.
  exact finiteColorSkewSpinorContraction
    (fun a b c : ColorIndex 2 => (M.structureConstant a b c : ℂ))
    hf
    (fun i : SpaceIndex => (((w ᵥ* M.gamma i) p.1 : ℝ) : ℂ))
    (fun i : SpaceIndex => (((w ᵥ* M.gamma i) q.1 : ℝ) : ℂ))
    (fun i k : SpaceIndex => (((w ᵥ* M.gammaTwo i k) q.1 : ℝ) : ℂ))
    (fun i k : SpaceIndex => (((w ᵥ* M.gammaTwo i k) p.1 : ℝ) : ℂ))
    (fun k c => ((x (k,c) : ℝ) : ℂ)) p.2 q.2

#print axioms sourceSpinorQuadraticPairWeight_eq_row
#print axioms sourceSpinorKineticWeight_eq_sourceRow
#print axioms finiteColorSelectorChannel
#print axioms finiteColorSkewSpinorContraction
#print axioms sourceAllSpinorResponsePoint_eq_originalRowKernel
#check @sourceAllSpinorResponsePoint_eq_originalRowKernel

end
end FCP.BFSSSU2PhysicalDomainL6G6F
