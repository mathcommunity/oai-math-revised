import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5AOriginalColorOneParameterStrongUnitaryGroupProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7TOriginalFullColorLieGaussIdentityProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7VActualSourceFullL2PhysicalFixedSpaceProbe

/-!
L6H5B — construct the *source-exact* densely-defined infinitesimal
Gauss candidate on the genuine original BFSS SmoothCore, then
verify its sign and pointwise coefficients in the original Fock fiber.

The candidate is J_F(c) f MINUS the +i forward boson gauge-orbit
vector derivative: U(g) uses boson g^{-1}.  The original finite
structureConstant and right-ordered position ∘ coordinateDerivative
operators are retained, as is the literal source Fock current.

This is an operator on source SmoothCore, whose image embeds in
the actual FullL2. Its identification with the strong-L2 derivative
of the full unitary orbit is a SEPARATE, UNPROVED domain theorem.
The independent physical fixed-subspace theorem does yield a
zero Hilbert-space derivative on actual invariant vectors;
that subspace must not be confused with a dense domain in FullL2.

No surrogate Fock field, novel axiom, source sign change,
self-adjointness or BFSS spectral claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainL6H5B
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G6I
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G6X
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6G7V
open FCP.BFSSSU2PhysicalDomainL6H5A

/-- True smooth-core color Gauss candidate with the original
+ i Fock generator and INVERSE bosonic-orbit sign. The original
bosonic coefficient multiplies after source coordinateDerivative. -/
noncomputable def actualOriginalCoreColorGaussCandidate
    (c : ColorIndex 2) : SmoothCore 2 →ₗ[ℂ] SmoothCore 2 :=
  (Complex.I : ℂ) • sourceOriginalFermionColorCurrent pairedAlgebraData c -
    ∑ p : SpaceIndex × ColorIndex 2, ∑ A : ColorIndex 2,
      (pairedAlgebraData.structureConstant p.2 A c : ℂ) •
        ((position (N := 2) p.1 A).comp
          (coordinateDerivative (N := 2) p.1 p.2))

/-- The candidate is a *genuine original test function*: its
canonical embedding into the full Hilbert space exists for EVERY
source SmoothCore vector, with no integrability axiom. -/
noncomputable def actualOriginalCoreColorGaussCandidateL2
    (c : ColorIndex 2) : SmoothCore 2 →ₗ[ℂ] FullL2 2 :=
  (coreToL2 (N := 2)).comp (actualOriginalCoreColorGaussCandidate c)

/-- The full source fiber generator and the right-ordered
finite bosonic source coefficient sum are recovered pointwise;
the plus/minus signs here define the candidate for the
INVERSE-pullback full-space original SU(2) action. -/
theorem actualOriginalCoreColorGaussCandidate_pointwise
    (c : ColorIndex 2) (f : SmoothCore 2) (x : Boson 2) :
    (actualOriginalCoreColorGaussCandidate c f) x =
      sourceFiberFermionColorGenerator pairedAlgebraData c (f x) -
        ∑ p : SpaceIndex × ColorIndex 2, ∑ A : ColorIndex 2,
          ((pairedAlgebraData.structureConstant p.2 A c : ℂ) *
            (x (p.1, A) : ℂ)) •
              ((coordinateDerivative (N := 2) p.1 p.2 f) x) := by
  -- Keep evaluation a named linear map. #260: unfolding the
  -- SmoothCore subtraction before evaluation leaves the source
  -- fermion-current rewrite syntactically hidden in the test function.
  let ev : SmoothCore 2 →ₗ[ℂ] Fermion 2 :=
    { toFun := fun u => u x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev (actualOriginalCoreColorGaussCandidate c f) = _
  simp only [actualOriginalCoreColorGaussCandidate,
    LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.comp_apply,
    map_sub, map_sum, map_smul]
  change
    (Complex.I • ((sourceOriginalFermionColorCurrent pairedAlgebraData c) f) x) -
      (∑ p : SpaceIndex × ColorIndex 2, ∑ A : ColorIndex 2,
        (pairedAlgebraData.structureConstant p.2 A c : ℂ) •
          ((position (N := 2) p.1 A)
            ((coordinateDerivative (N := 2) p.1 p.2 f))) x) =
      sourceFiberFermionColorGenerator pairedAlgebraData c (f x) -
        ∑ p : SpaceIndex × ColorIndex 2, ∑ A : ColorIndex 2,
          ((pairedAlgebraData.structureConstant p.2 A c : ℂ) *
            (x (p.1, A) : ℂ)) •
              ((coordinateDerivative (N := 2) p.1 p.2 f) x)
  rw [sourceFermionColorCurrent_apply_fiber]
  change
    sourceFiberFermionColorGenerator pairedAlgebraData c (f x) -
      (∑ p : SpaceIndex × ColorIndex 2, ∑ A : ColorIndex 2,
        (pairedAlgebraData.structureConstant p.2 A c : ℂ) •
          ((position (N := 2) p.1 A)
            ((coordinateDerivative (N := 2) p.1 p.2 f))) x) =
      _
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro A _
  change
    (pairedAlgebraData.structureConstant p.2 A c : ℂ) •
      ((x (p.1, A) : ℂ) •
        ((coordinateDerivative (N := 2) p.1 p.2 f) x)) =
    ((pairedAlgebraData.structureConstant p.2 A c : ℂ) *
      (x (p.1, A) : ℂ)) •
        ((coordinateDerivative (N := 2) p.1 p.2 f) x)
  exact (smul_smul
    (pairedAlgebraData.structureConstant p.2 A c : ℂ)
    (x (p.1, A) : ℂ)
    (((coordinateDerivative (N := 2) p.1 p.2 f) x) : Fermion 2))

/-- A true FullL2 norm-derivative, already provable on the
ORIGINAL physical fixed subspace (not asserted dense in FullL2).
This tests actual source U(g), not a proxy representation. -/
theorem actualOriginalPhysicalColorCurve_hasDerivAt_zero
    (c : ColorIndex 2) (v : FullL2 2)
    (hv : v ∈ pairedGaugeData.physicalSpace) :
    HasDerivAt
      (fun t : ℝ =>
        actualOriginalFullL2GaugePairCLM (sourcePlusIGaugeCurve c t) v)
      (0 : FullL2 2) 0 := by
  have hfixed :
      ∀ t : ℝ,
        actualOriginalFullL2GaugePairCLM
          (sourcePlusIGaugeCurve c t) v = v := by
    intro t
    exact (actualOriginalFullL2GaugePair_fixed_iff_physical v).2 hv _
  have heq :
      (fun t : ℝ =>
        actualOriginalFullL2GaugePairCLM (sourcePlusIGaugeCurve c t) v) =
      (fun _ : ℝ => v) := by
    funext t
    exact hfixed t
  rw [heq]
  exact hasDerivAt_const 0 v

#print axioms actualOriginalCoreColorGaussCandidate
#print axioms actualOriginalCoreColorGaussCandidateL2
#print axioms actualOriginalCoreColorGaussCandidate_pointwise
#print axioms actualOriginalPhysicalColorCurve_hasDerivAt_zero
#check @actualOriginalCoreColorGaussCandidateL2
#check @actualOriginalCoreColorGaussCandidate_pointwise
#check @actualOriginalPhysicalColorCurve_hasDerivAt_zero

end
end FCP.BFSSSU2PhysicalDomainL6H5B
