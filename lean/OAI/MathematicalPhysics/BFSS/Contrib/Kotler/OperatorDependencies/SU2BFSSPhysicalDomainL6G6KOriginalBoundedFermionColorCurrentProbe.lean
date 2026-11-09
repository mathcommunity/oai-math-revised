import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6JOriginalFermionColorCurrentCARProbe

/-!
L6G6K — the ORIGINAL bounded fiber color current, its precise source
SmoothCore recovery, Hermiticity, and CAR action. No surrogate Fock
space or assumed representation generator is introduced.

The skew generator i G_F is a bounded operator on the original
Fermion 2 Hilbert space. Its exponential/gauge identification and
vacuum normalization remain separate obligations.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G6K
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G6I
open FCP.BFSSSU2PhysicalDomainL6G6J

abbrev SourceFiberEnd := Fermion 2 →L[ℂ] Fermion 2

/-- One literal ordered pair of the source bounded Majoranas. -/
def sourceFiberFermionColorTerm (M : AlgebraData 2)
    (c : ColorIndex 2) (s : SpinIndex) (a b : ColorIndex 2) :
    SourceFiberEnd :=
  (M.structureConstant a b c : ℂ) • (M.theta s a * M.theta s b)

/-- The same -i/2 normalized current on the original bounded fiber. -/
def sourceFiberFermionColorCurrent (M : AlgebraData 2)
    (c : ColorIndex 2) : SourceFiberEnd :=
  (-Complex.I / 2 : ℂ) •
    (∑ s : SpinIndex, ∑ a : ColorIndex 2, ∑ b : ColorIndex 2,
      sourceFiberFermionColorTerm M c s a b)

private def evalSourceEnd (f : SmoothCore 2) (x : Boson 2) :
    SourceEnd 2 →ₗ[ℂ] Fermion 2 where
  toFun T := (T f) x
  map_add' _A _B := rfl
  map_smul' _z _A := rfl

private def evalSourceFiber (v : Fermion 2) :
    SourceFiberEnd →ₗ[ℂ] Fermion 2 where
  toFun T := T v
  map_add' _A _B := rfl
  map_smul' _z _A := rfl

/-- Exact ordered-pair recovery, before any finite-sum transport. -/
theorem sourceFermionColorTerm_apply_fiber (M : AlgebraData 2)
    (c : ColorIndex 2) (s : SpinIndex) (a b : ColorIndex 2)
    (f : SmoothCore 2) (x : Boson 2) :
    ((sourceOriginalFermionColorTerm M c s a b) f) x =
      sourceFiberFermionColorTerm M c s a b (f x) := rfl

/-- The literal source SmoothCore current acts pointwise by the exact
bounded fiber current. No color, gamma or gauge premise is required. -/
theorem sourceFermionColorCurrent_apply_fiber (M : AlgebraData 2)
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    ((sourceOriginalFermionColorCurrent M c) f) x =
      sourceFiberFermionColorCurrent M c (f x) := by
  change (evalSourceEnd f x) (sourceOriginalFermionColorCurrent M c) =
    (evalSourceFiber (f x)) (sourceFiberFermionColorCurrent M c)
  simp only [sourceOriginalFermionColorCurrent,
    sourceFiberFermionColorCurrent, map_smul, map_sum]
  apply congrArg (fun v : Fermion 2 => (-Complex.I / 2 : ℂ) • v)
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact sourceFermionColorTerm_apply_fiber M c s a b f x

/-- Exact equality to the pinned TestFunction.postcompCLM expression;
this is the required source bridge, not a replacement current. -/
theorem sourceFermionColorCurrent_eq_postcomp (M : AlgebraData 2)
    (c : ColorIndex 2) :
    sourceOriginalFermionColorCurrent M c =
      (TestFunction.postcompCLM (sourceFiberFermionColorCurrent M c)).toLinearMap := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  exact sourceFermionColorCurrent_apply_fiber M c f x

/-- The literal source theta field already has delta-one bounded CAR. -/
private theorem sourceFiberTheta_CAR (M : AlgebraData 2)
    (s u : SpinIndex) (a b : ColorIndex 2) :
    M.theta s a * M.theta u b + M.theta u b * M.theta s a =
      if s = u ∧ a = b then (1 : SourceFiberEnd) else 0 := by
  classical
  by_cases h : s = u ∧ a = b
  · simpa only [_root_.ite_eq_left h, one_smul] using M.theta_CAR s u a b
  · simpa only [_root_.ite_eq_right h, zero_nsmul] using M.theta_CAR s u a b

/-- The bounded current has the same exact source-normalized CAR
action. Its connection to GaugeData.fermion is still not assumed. -/
theorem sourceFiberFermionColorCurrent_comm (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (c : ColorIndex 2) (t : SpinIndex) (d : ColorIndex 2) :
    sourceFiberFermionColorCurrent M c * M.theta t d -
      M.theta t d * sourceFiberFermionColorCurrent M c =
      Complex.I • (∑ b : ColorIndex 2,
        (M.structureConstant d b c : ℂ) • M.theta t b) := by
  classical
  have hskew (a b e : ColorIndex 2) :
      (M.structureConstant b a e : ℂ) =
        -(M.structureConstant a b e : ℂ) := by
    simpa only [Complex.ofReal_neg] using
      congrArg (fun r : ℝ => (r : ℂ))
        (FCP.BFSSSU2PhysicalDomainL6G6D.sourceSU2StructureConstant_swapFirst
          M hcolor a b e)
  unfold sourceFiberFermionColorCurrent
  exact finiteCARColorCurrent_namedTerms_interface
    (R := SourceFiberEnd) (S := SpinIndex) (C := ColorIndex 2)
    M.theta (sourceFiberTheta_CAR M)
    (fun a b e => (M.structureConstant a b e : ℂ)) hskew
    c (fun s a b => sourceFiberFermionColorTerm M c s a b)
    (fun _ _ _ => rfl) t d

/-- The additive star equivalence commutes with finite sums. Keep
this universe-polymorphic interface at module scope. -/
private theorem finiteStar_sum {R I : Type*}
    [AddCommMonoid R] [StarAddMonoid R] [Fintype I] (T : I → R) :
    star (∑ i : I, T i) = ∑ i : I, star (T i) := by
  exact map_sum (starAddEquiv : R ≃+ R) _ _

/-- A real skew quadratic form in self-adjoint generators is skew.
Prove this in an abstract star algebra before passing to BFSS. -/
private theorem finiteRealSkewThetaQuadratic_star
    {R S C : Type*} [Ring R] [StarRing R]
    [Algebra ℂ R] [StarModule ℂ R] [Fintype S] [Fintype C]
    (theta : S → C → R) (htheta : ∀ s a, star (theta s a) = theta s a)
    (F : C → C → ℝ) (hskew : ∀ a b, F b a = -F a b) :
    star (∑ s : S, ∑ a : C, ∑ b : C,
      (F a b : ℂ) • (theta s a * theta s b)) =
      -(∑ s : S, ∑ a : C, ∑ b : C,
        (F a b : ℂ) • (theta s a * theta s b)) := by
  have hcoeff (a b : C) : star (F a b : ℂ) = (F a b : ℂ) := by
    rw [RCLike.star_def]
    exact RCLike.conj_ofReal (F a b)
  calc
    _ = ∑ s : S, ∑ a : C, ∑ b : C,
      (F a b : ℂ) • (theta s b * theta s a) := by
        simp only [finiteStar_sum, star_smul, star_mul, htheta, hcoeff]
    _ = ∑ s : S, ∑ a : C, ∑ b : C,
      (F b a : ℂ) • (theta s a * theta s b) := by
        apply Finset.sum_congr rfl
        intro s _
        exact Finset.sum_comm
    _ = ∑ s : S, ∑ a : C, ∑ b : C,
      -((F a b : ℂ) • (theta s a * theta s b)) := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [hskew a b]
        simp only [Complex.ofReal_neg, neg_smul]
    _ = _ := by simp only [Finset.sum_neg_distrib]

/-- Keep literal source summands named during the bounded-fiber
specialization, with every recovery equality explicitly proved. -/
private theorem finiteRealSkewThetaNamedQuadratic_star
    {R S C : Type*} [Ring R] [StarRing R]
    [Algebra ℂ R] [StarModule ℂ R] [Fintype S] [Fintype C]
    (theta : S → C → R) (htheta : ∀ s a, star (theta s a) = theta s a)
    (F : C → C → ℝ) (hskew : ∀ a b, F b a = -F a b)
    (T : S → C → C → R)
    (hT : ∀ s a b, T s a b = (F a b : ℂ) • (theta s a * theta s b)) :
    star (∑ s : S, ∑ a : C, ∑ b : C, T s a b) =
      -(∑ s : S, ∑ a : C, ∑ b : C, T s a b) := by
  have hsum : (∑ s : S, ∑ a : C, ∑ b : C, T s a b) =
      ∑ s : S, ∑ a : C, ∑ b : C,
        (F a b : ℂ) • (theta s a * theta s b) := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact hT s a b
  rw [hsum]
  exact finiteRealSkewThetaQuadratic_star theta htheta F hskew

/-- Hermiticity of the exact bounded source current, using source
self-adjoint theta and source color antisymmetry, with no CAR premise. -/
theorem sourceFiberFermionColorCurrent_selfAdjoint (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (c : ColorIndex 2) :
    IsSelfAdjoint (sourceFiberFermionColorCurrent M c) := by
  have hskew (a b : ColorIndex 2) :
      M.structureConstant b a c = -M.structureConstant a b c :=
    FCP.BFSSSU2PhysicalDomainL6G6D.sourceSU2StructureConstant_swapFirst
      M hcolor a b c
  have hs := finiteRealSkewThetaNamedQuadratic_star
    (R := SourceFiberEnd) (S := SpinIndex) (C := ColorIndex 2)
    M.theta (fun s a => (M.theta_selfAdjoint s a).star_eq)
    (fun a b => M.structureConstant a b c) hskew
    (fun s a b => sourceFiberFermionColorTerm M c s a b)
    (fun _ _ _ => rfl)
  change star ((-Complex.I / 2 : ℂ) •
    (∑ s : SpinIndex, ∑ a : ColorIndex 2, ∑ b : ColorIndex 2,
      sourceFiberFermionColorTerm M c s a b)) =
    (-Complex.I / 2 : ℂ) •
    (∑ s : SpinIndex, ∑ a : ColorIndex 2, ∑ b : ColorIndex 2,
      sourceFiberFermionColorTerm M c s a b)
  rw [star_smul, hs, smul_neg, ← neg_smul]
  congr 1
  simp [neg_div]

/-- The precise source generator for the +i Pauli gauge curve. -/
def sourceFiberFermionColorGenerator (M : AlgebraData 2)
    (c : ColorIndex 2) : SourceFiberEnd :=
  Complex.I • sourceFiberFermionColorCurrent M c

theorem sourceFiberFermionColorGenerator_star_eq_neg (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (c : ColorIndex 2) :
    star (sourceFiberFermionColorGenerator M c) =
      -sourceFiberFermionColorGenerator M c := by
  unfold sourceFiberFermionColorGenerator
  rw [star_smul, (sourceFiberFermionColorCurrent_selfAdjoint M hcolor c).star_eq]
  simp only [Complex.star_def, Complex.conj_I]
  -- The remaining goal is scalar-negation transport, not a new CAR identity.
  exact neg_smul Complex.I (sourceFiberFermionColorCurrent M c)

#print axioms sourceFermionColorTerm_apply_fiber
#print axioms sourceFermionColorCurrent_apply_fiber
#print axioms sourceFermionColorCurrent_eq_postcomp
#print axioms sourceFiberTheta_CAR
#print axioms sourceFiberFermionColorCurrent_comm
#print axioms finiteStar_sum
#print axioms finiteRealSkewThetaQuadratic_star
#print axioms finiteRealSkewThetaNamedQuadratic_star
#print axioms sourceFiberFermionColorCurrent_selfAdjoint
#print axioms sourceFiberFermionColorGenerator_star_eq_neg
#check @sourceFermionColorCurrent_eq_postcomp
#check @sourceFiberFermionColorCurrent_comm
#check @sourceFiberFermionColorGenerator_star_eq_neg

end
end FCP.BFSSSU2PhysicalDomainL6G6K
