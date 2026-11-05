import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6COriginalFermionResponseKroneckerSelectorProbe

/-!
L6G6D — actual original BFSS SU(2) quadratic source coefficient
is symmetric in its TWO bosonic position labels. The structure
constant is antisymmetric and the source gamma bivector is also
antisymmetric, so their PRODUCT is symmetric.

Consequence: the two Kronecker derivative legs proven in G6C
are equal and the exact point-response coefficient is TWICE the
first-leg sum. This preserves the source -i and 1/2 weights.
No original theta product is reordered; the Fierz contraction
and full fermionic Gauss identity remain subsequent obligations.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G6D
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G4B
open FCP.BFSSSU2PhysicalDomainL6G6A
open FCP.BFSSSU2PhysicalDomainL6G6C

/-- Skew exchange of the ORIGINAL source gamma bivector's
spatial labels. It is an exact definitional consequence of
its commutator definition, not an extra Clifford premise. -/
theorem sourceGammaTwo_swapOriginal {N : ℕ}
    (M : AlgebraData N) (i j : SpaceIndex) :
    M.gammaTwo j i = -M.gammaTwo i j := by
  change (1 / 2 : ℝ) • (M.gamma j * M.gamma i - M.gamma i * M.gamma j) =
    -((1 / 2 : ℝ) • (M.gamma i * M.gamma j - M.gamma j * M.gamma i))
  rw [← smul_neg, neg_sub]

/-- Antisymmetry of the source color bracket implies skewness in the
two bracket labels for ANY original AlgebraData, not only SU(2).
Avoid a 27-case evaluation of the explicit Pauli epsilon tensor. -/
theorem sourceSU2StructureConstant_swapLast
    (M : AlgebraData 2)
    (_hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (a b c : ColorIndex 2) :
    M.structureConstant a c b = -M.structureConstant a b c := by
  have hbracket (X Y : ColorMatrix 2) :
      AlgebraData.bracket Y X = -AlgebraData.bracket X Y := by
    unfold AlgebraData.bracket
    rw [← smul_neg, neg_sub]
  change (Matrix.trace (M.color a *
      AlgebraData.bracket (M.color c) (M.color b))).re =
    -(Matrix.trace (M.color a *
      AlgebraData.bracket (M.color b) (M.color c))).re
  rw [hbracket, mul_neg, Matrix.trace_neg, Complex.neg_re]

/-- For normalized Pauli color, the ORIGINAL accepted epsilon3 cyclic
identity transports final-two skewness to first-two skewness.
No re-evaluation of the 27 source color cases is needed. -/
theorem sourceSU2StructureConstant_swapFirst
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (a b c : ColorIndex 2) :
    M.structureConstant b a c = -M.structureConstant a b c := by
  calc
    M.structureConstant b a c =
        Real.sqrt 2 * FCP.BFSSSU2.epsilon3 b a c :=
          FCP.BFSSSU2.algebraData_structureConstant_of_pauli_color M hcolor b a c
    _ = Real.sqrt 2 * FCP.BFSSSU2.epsilon3 a c b := by
      rw [FCP.BFSSSU2.epsilon3_cyclic]
    _ = M.structureConstant a c b :=
      (FCP.BFSSSU2.algebraData_structureConstant_of_pauli_color M hcolor a c b).symm
    _ = -M.structureConstant a b c :=
      sourceSU2StructureConstant_swapLast M hcolor a b c

/-- Each original ordered quadratic weight is symmetric in its
two BOSONIC labels, while its spinor and fermionic-color labels
are unchanged. This preserves the full source 1/2 normalization. -/
theorem sourceQuadraticWeight_pairSymmetric
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (α : SpinIndex) (p : FermionLabel 2)
    (v t : BosonLabel 2) :
    sourceQuadraticWeight M α p t v =
      sourceQuadraticWeight M α p v t := by
  have hf := sourceSU2StructureConstant_swapLast M hcolor p.2 v.2 t.2
  have hg := congrArg
    (fun G : GammaMatrix => G α p.1) (sourceGammaTwo_swapOriginal M v.1 t.1)
  simp only [Matrix.neg_apply] at hg
  unfold sourceQuadraticWeight
  rw [hf, hg]
  congr 1
  ring

/-- Literal first leg of the source-selected commutator response;
this is not a surrogate coefficient, only an abbreviation for the
already accepted G6C polynomial's first finite sum. -/
def sourceCoefficientResponseFirstLeg
    (M : AlgebraData 2) (α β : SpinIndex)
    (p q : FermionLabel 2) (x : Boson 2) : ℂ :=
  ∑ u : BosonLabel 2, ∑ t : BosonLabel 2,
    (sourceKineticWeight M α p u * sourceQuadraticWeight M β q u t -
      sourceKineticWeight M β q u * sourceQuadraticWeight M α p u t) *
        ((x t : ℝ) : ℂ)

/-- General finite proof of the factor of TWO when both quadratic
derivative labels are symmetric. Do this abstractly so Lean never
normalizes the full concrete BFSS coefficient during `change`. -/
private theorem finiteSymmetricQuadraticResponse_twice
    {I : Type*} [Fintype I]
    (K L : I → ℂ) (Q R : I → I → ℂ) (x : I → ℂ)
    (hQ : ∀ u t, Q t u = Q u t)
    (hR : ∀ u t, R t u = R u t) :
    (∑ u : I,
      ((∑ t : I, (K u * Q u t - L u * R u t) * x t) +
       (∑ t : I, (K u * Q t u - L u * R t u) * x t))) =
    (2 : ℂ) * ∑ u : I, ∑ t : I,
      (K u * Q u t - L u * R u t) * x t := by
  have hlegs (u : I) :
      (∑ t : I, (K u * Q t u - L u * R t u) * x t) =
        ∑ t : I, (K u * Q u t - L u * R u t) * x t := by
    apply Finset.sum_congr rfl
    intro t _
    rw [hQ u t, hR u t]
  calc
    _ = ∑ u : I,
          ((∑ t : I, (K u * Q u t - L u * R u t) * x t) +
           (∑ t : I, (K u * Q u t - L u * R u t) * x t)) := by
            apply Finset.sum_congr rfl
            intro u _
            rw [hlegs u]
    _ = ∑ u : I,
          (2 : ℂ) * (∑ t : I, (K u * Q u t - L u * R u t) * x t) := by
            apply Finset.sum_congr rfl
            intro u _
            ring
    _ = _ := by rw [Finset.mul_sum]

/-- The TWO original position-derivative legs coincide after
source weight symmetry: an exact factor of 2, no silently discarded
Kronecker term or operator interchange. -/
theorem sourceCoefficientResponseSelected_eq_twice_first
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (α β : SpinIndex) (p q : FermionLabel 2)
    (x : Boson 2) :
    sourceCoefficientResponseSelected M α β p q x =
      (2 : ℂ) * sourceCoefficientResponseFirstLeg M α β p q x := by
  unfold sourceCoefficientResponseSelected sourceCoefficientResponseFirstLeg
  exact finiteSymmetricQuadraticResponse_twice
    (sourceKineticWeight M α p) (sourceKineticWeight M β q)
    (sourceQuadraticWeight M β q) (sourceQuadraticWeight M α p)
    (fun t => ((x t : ℝ) : ℂ))
    (sourceQuadraticWeight_pairSymmetric M hcolor β q)
    (sourceQuadraticWeight_pairSymmetric M hcolor α p)

/-- Pass the exact source two-leg reduction through G6C's
unchanged original response polynomial. -/
theorem sourceCoefficientResponsePoint_eq_twice_first
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (α β : SpinIndex) (p q : FermionLabel 2)
    (x : Boson 2) :
    sourceCoefficientResponsePoint M α β p q x =
      (2 : ℂ) * sourceCoefficientResponseFirstLeg M α β p q x := by
  rw [sourceCoefficientResponsePoint_eq_selected]
  exact sourceCoefficientResponseSelected_eq_twice_first M hcolor α β p q x

#print axioms sourceGammaTwo_swapOriginal
#print axioms sourceSU2StructureConstant_swapLast
#print axioms sourceSU2StructureConstant_swapFirst
#print axioms sourceQuadraticWeight_pairSymmetric
#print axioms finiteSymmetricQuadraticResponse_twice
#print axioms sourceCoefficientResponseSelected_eq_twice_first
#print axioms sourceCoefficientResponsePoint_eq_twice_first
#check @sourceCoefficientResponsePoint_eq_twice_first

end
end FCP.BFSSSU2PhysicalDomainL6G6D
