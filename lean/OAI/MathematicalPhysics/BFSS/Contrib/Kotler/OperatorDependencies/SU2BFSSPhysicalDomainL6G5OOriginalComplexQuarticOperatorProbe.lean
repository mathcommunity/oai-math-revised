import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G5NOriginalFiniteQuarticContractionProbe

/-!
L6G5O — lift the now-qualified finite REAL source quartic
contraction to the original COMPLEX source coefficient and genuine
SmoothCore quadratic-position operator. All operators and coefficients
are the original pinned source (no surrogate, no domain extension).

Scope: only the bosonic quadratic-position square, under explicit
original normalized-Pauli color. Orbital Gauss, fermionic Gauss,
complete Hamiltonian identity and spectrum remain separate.
-/
set_option autoImplicit false
namespace FCP.BFSSSU2PhysicalDomainL6G5O
noncomputable section
open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G2
open FCP.BFSSSU2PhysicalDomainL6G3
open FCP.BFSSSU2PhysicalDomainL6G5E
open FCP.BFSSSU2PhysicalDomainL6G5F
open FCP.BFSSSU2PhysicalDomainL6G5I
open FCP.BFSSSU2PhysicalDomainL6G5N

/-- The requested source complex coefficient-square identity: REAL
L6G5N cast to the original source coefficient, with no dropped
1/2, gammaTwo, spinor labels, or color factors. -/
theorem sourceSU2FiniteQuarticComplex
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (w : SpinIndex → ℝ) (x : Boson 2) :
    (1 / 2 : ℂ) *
      (∑ p : FermionLabel 2,
        sourceQuadraticPointCoefficient M w p x *
          sourceQuadraticPointCoefficient M w p x) =
        (spinorSquareNorm w : ℂ) *
          (sourceNineSpatialQuarticPotential M x : ℂ) := by
  classical
  have hcast := congrArg (fun t : ℝ => (t : ℂ))
    (sourceSU2FiniteQuarticReal M hcolor w x)
  simp only [Complex.ofReal_mul, Complex.ofReal_sum,
    Complex.ofReal_pow] at hcast
  have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf] at hcast
  simpa only [sourceQuadraticPointCoefficient_eq_real, pow_two]
    using hcast

/-- Source quadratic-position square, evaluated on every ORIGINAL
SmoothCore test function and original bosonic configuration, is
exactly twice ||w||² times the ORIGINAL full nine-space potential.
The displayed half-square has the literal CAR normal-order factor. -/
theorem sourceSU2QuadraticSquare_potential_apply
    (M : AlgebraData 2)
    (hcolor : ∀ a : ColorIndex 2,
      M.color a = FCP.BFSSSU2.normalizedPauli a)
    (w : SpinIndex → ℝ)
    (f : SmoothCore 2) (x : Boson 2) :
    (((1 / 2 : ℂ) • sourceSpinorQuadraticSquare M w) f) x =
      ((spinorSquareNorm w : ℂ) *
        (sourceNineSpatialQuarticPotential M x : ℂ)) • f x := by
  change (1 / 2 : ℂ) • ((sourceSpinorQuadraticSquare M w f) x) = _
  rw [sourceSpinorQuadraticSquare_apply]
  rw [smul_smul]
  rw [sourceSU2FiniteQuarticComplex M hcolor w x]

#print axioms sourceSU2FiniteQuarticComplex
#print axioms sourceSU2QuadraticSquare_potential_apply
#check @sourceSU2QuadraticSquare_potential_apply
end
end FCP.BFSSSU2PhysicalDomainL6G5O
