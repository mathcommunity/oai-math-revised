import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5UOriginalMixedPointCoefficientProbe

/-!
L6G5V — genuine original right-ordered mixed SmoothCore differential
expression, not merely a generic coefficient reconstruction.

Preserve original W*K ordering; evaluate source W as multiplication
ONLY AFTER it acts on K*f; contract the exact -Complex.I kinetic
weight and the source quadratic W point coefficient using L6G5U.
The surviving expression is +i times the genuine source bracket
times w^T gamma w, applied to the original source coordinate derivative.

This does NOT silently assert that the operator vanishes, equals the
full Gauss operator, or validates any spectral statement.
-/

set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5V
noncomputable section
open scoped Matrix BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G1
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G4A
open FCP.BFSSSU2PhysicalDomainL6G5B
open FCP.BFSSSU2PhysicalDomainL6G5C
open FCP.BFSSSU2PhysicalDomainL6G5D
open FCP.BFSSSU2PhysicalDomainL6G5F
open FCP.BFSSSU2PhysicalDomainL6G5I
open FCP.BFSSSU2PhysicalDomainL6G5P
open FCP.BFSSSU2PhysicalDomainL6G5U

/-- Finite color selector contracts to its actual source color,
retaining the -i factor and the original real polynomial. -/
private theorem finiteMixedColorSelector
    {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]
    (a : C) (F : S → C → ℝ) (g : S → ℝ) :
    (∑ p : S × C,
      (F p.1 p.2 : ℂ) *
        (if a = p.2 then -Complex.I * (g p.1 : ℂ) else 0)) =
      -Complex.I * ((∑ β : S, g β * F β a : ℝ) : ℂ) := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    (∑ β : S, ∑ c : C, (F β c : ℂ) *
        (if a = c then -Complex.I * (g β : ℂ) else 0)) =
      ∑ β : S, (F β a : ℂ) * (-Complex.I * (g β : ℂ)) := by
        apply Finset.sum_congr rfl
        intro β _
        simp [mul_ite]
    _ = _ := by
      simp only [Complex.ofReal_sum, Complex.ofReal_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro β _
      ring

/-- ACTUAL original complex kinetic/quadratic scalar coefficient:
the -i kinetic weight converts L6G5U's negative real mixed
contraction to POSITIVE i times the source bracket. Every original
fermion and color label is included. No Pauli restriction is needed
for this finite coefficient identity. -/
theorem sourceOriginalMixedComplexCoefficient_contract
    {N : ℕ} (M : AlgebraData N)
    (hgamma : M.gamma = originalGamma)
    (w : SpinIndex → ℝ) (x : Boson N)
    (u : BosonLabel N) :
    (∑ p : FermionLabel N,
      sourceQuadraticPointCoefficient M w p x *
        sourceSpinorKineticWeight M w p u) =
      Complex.I * ((∑ k : SpaceIndex,
        M.coordinateBracketAll x u.1 k u.2 *
          dotProduct w (M.gamma k *ᵥ w) : ℝ) : ℂ) := by
  classical
  calc
    _ = ∑ p : FermionLabel N,
      (sourceQuadraticPointReal M w p x : ℂ) *
        (if u.2 = p.2 then -Complex.I *
          (((w ᵥ* originalGamma u.1) p.1 : ℝ) : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro p _
            rw [sourceQuadraticPointCoefficient_eq_real,
              sourceSpinorKineticWeight_eq M w hgamma]
    _ = -Complex.I *
      ((∑ β : SpinIndex,
        ((w ᵥ* originalGamma u.1) β) *
          sourceQuadraticPointReal M w (β,u.2) x : ℝ) : ℂ) := by
          exact finiteMixedColorSelector u.2
            (fun β a => sourceQuadraticPointReal M w (β,a) x)
            (fun β => (w ᵥ* originalGamma u.1) β)
    _ = _ := by
      rw [← hgamma]
      rw [sourceOriginalMixedPointCoefficient_contract M hgamma w x u.1 u.2]
      simp only [Complex.ofReal_neg]
      ring

/-- Evaluation at one original SmoothCore function and bosonic
configuration is linear in the actual original source endomorphism. -/
private def evalOriginalSourceEnd {N : ℕ}
    (f : SmoothCore N) (x : Boson N) :
    SourceEnd N →ₗ[ℂ] Fermion N where
  toFun A := (A f) x
  map_add' A B := by rfl
  map_smul' c A := by rfl

/-- Original source -i kinetic differential evaluated without
changing the order of any multiplication/differential operator. -/
private theorem sourceSpinorKinetic_apply
    {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) (p : FermionLabel N)
    (f : SmoothCore N) (x : Boson N) :
    (sourceSpinorKineticDifferential M w p f) x =
      ∑ u : BosonLabel N,
        sourceSpinorKineticWeight M w p u • ((sourceD u f) x) := by
  change (evalOriginalSourceEnd f x)
    (sourceSpinorKineticDifferential M w p) = _
  unfold sourceSpinorKineticDifferential
  simp only [map_sum, map_smul]
  rfl

/-- Literal right ordering at each fermion label: source W acts
pointwise ON THE RESULT of K*f, never on f before K acts. -/
private theorem sourceRightOrderedAtom_apply
    {N : ℕ} (M : AlgebraData N)
    (w : SpinIndex → ℝ) (p : FermionLabel N)
    (f : SmoothCore N) (x : Boson N) :
    ((sourceSpinorQuadraticMultiplication M w p *
        sourceSpinorKineticDifferential M w p) f) x =
      ∑ u : BosonLabel N,
        (sourceQuadraticPointCoefficient M w p x *
          sourceSpinorKineticWeight M w p u) •
            ((sourceD u f) x) := by
  change (sourceSpinorQuadraticMultiplication M w p
      (sourceSpinorKineticDifferential M w p f)) x = _
  rw [sourceSpinorQuadraticMultiplication_apply]
  rw [sourceSpinorKinetic_apply]
  simp only [Finset.smul_sum, smul_smul]

/-- Final original smooth-core ordered mixed operator evaluation:
the scalar part is precisely +i times the source coordinate bracket
and spinor vector coefficient. No surrogate Hilbert domain or
invented Gauss cancellation. -/
theorem sourceSpinorRightOrderedMixed_originalApply
    {N : ℕ} (M : AlgebraData N)
    (hgamma : M.gamma = originalGamma)
    (w : SpinIndex → ℝ)
    (f : SmoothCore N) (x : Boson N) :
    ((sourceSpinorRightOrderedMixed M w) f) x =
      ∑ u : BosonLabel N,
        (Complex.I * ((∑ k : SpaceIndex,
          M.coordinateBracketAll x u.1 k u.2 *
            dotProduct w (M.gamma k *ᵥ w) : ℝ) : ℂ)) •
              ((sourceD u f) x) := by
  classical
  calc
    _ = ∑ p : FermionLabel N, ∑ u : BosonLabel N,
      (sourceQuadraticPointCoefficient M w p x *
        sourceSpinorKineticWeight M w p u) •
          ((sourceD u f) x) := by
            change (evalOriginalSourceEnd f x)
              (sourceSpinorRightOrderedMixed M w) = _
            unfold sourceSpinorRightOrderedMixed
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro p _
            exact sourceRightOrderedAtom_apply M w p f x
    _ = ∑ u : BosonLabel N, ∑ p : FermionLabel N,
      (sourceQuadraticPointCoefficient M w p x *
        sourceSpinorKineticWeight M w p u) •
          ((sourceD u f) x) := Finset.sum_comm
    _ = ∑ u : BosonLabel N,
      (∑ p : FermionLabel N,
        sourceQuadraticPointCoefficient M w p x *
          sourceSpinorKineticWeight M w p u) •
            ((sourceD u f) x) := by
              simp only [Finset.sum_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [sourceOriginalMixedComplexCoefficient_contract M hgamma w x u]

#print axioms finiteMixedColorSelector
#print axioms sourceOriginalMixedComplexCoefficient_contract
#print axioms sourceSpinorKinetic_apply
#print axioms sourceRightOrderedAtom_apply
#print axioms sourceSpinorRightOrderedMixed_originalApply
#check @sourceSpinorRightOrderedMixed_originalApply
end
end FCP.BFSSSU2PhysicalDomainL6G5V
