import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1AOriginalSpin48KernelCommutantProbe
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! Owner import from FCP cc608e2282e1b32bb11bbb64424e4775b28138e2,
original source blob 7334a3616740b902c9e42231efc97ed7566ad8c2.
Only imports and this provenance comment are adapted. Definitions, theorem
statements and proof bodies below are source-exact. Local candidate only
until an independent owner strict gate passes. -/

/-!
K1C — source-exact original 48-real Clifford polar contraction bridge.

The genuine pinned Clifford grade involution, original source polar
quadratic pairing, and CliffordAlgebra.contractLeft provide a uniform
graded commutator identity for all original source Clifford elements.
For an EVEN Spin element its graded commutator is the ordinary
commutator, so K1A's accepted trivial-action criterion implies
annihilation by every original source polar contraction.

This does NOT say that all such annihilated elements are scalar;
that separate exterior/PBW coefficient separation lemma remains open.
No full two-sign kernel, covering, Spin9 lift or spectral claim.

Prospective until fresh pinned strict Lean/axiom acceptance.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52K1C
noncomputable section

open FCP.BFSSS1V0

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic
private abbrev C := CliffordAlgebra Q

/-- Exact original Clifford graded commutator is native left contraction
by the source quadratic polar functional, for ALL Clifford elements. -/
theorem originalSourceClifford_gradedCommutator_eq_polarContraction
    (v : Source48Vector) (x : C) :
    CliffordAlgebra.ι Q v * x -
        CliffordAlgebra.involute x * CliffordAlgebra.ι Q v =
      CliffordAlgebra.contractLeft (Q.polarBilin v) x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      have hr :
          CliffordAlgebra.involute (algebraMap ℝ C r) =
            algebraMap ℝ C r :=
        (CliffordAlgebra.involute : C →ₐ[ℝ] C).commutes r
      rw [hr, CliffordAlgebra.contractLeft_algebraMap]
      rw [Algebra.commutes r (CliffordAlgebra.ι Q v)]
      exact sub_self _
  | add x y hx hy =>
      simp only [mul_add, map_add, add_mul]
      rw [← hx, ← hy]
      abel
  | ι_mul u x hx =>
      rw [map_mul, CliffordAlgebra.involute_ι,
        CliffordAlgebra.contractLeft_ι_mul]
      rw [← mul_assoc (CliffordAlgebra.ι Q v)
        (CliffordAlgebra.ι Q x) u,
        CliffordAlgebra.ι_mul_ι_comm v x]
      rw [← hx]
      simp only [neg_mul, sub_mul, mul_sub, Algebra.smul_def,
        QuadraticMap.polarBilin_apply_apply]
      noncomm_ring

/-- For an original EVEN Clifford element, the commutator with every
source real vector generator equals that source polar contraction. -/
theorem originalSourceClifford_evenCommutator_eq_polarContraction
    (v : Source48Vector) (x : C)
    (hx : x ∈ CliffordAlgebra.even Q) :
    CliffordAlgebra.ι Q v * x - x * CliffordAlgebra.ι Q v =
      CliffordAlgebra.contractLeft (Q.polarBilin v) x := by
  simpa only [CliffordAlgebra.involute_eq_of_mem_even hx]
    using originalSourceClifford_gradedCommutator_eq_polarContraction v x

/-- An original Spin48 group element in K1A's REAL vector-action
kernel is annihilated by ALL native polar contractions. -/
theorem originalSourceSpin48_trivialAction_polarContractions_zero
    (s : spinGroup Q)
    (hs : ∀ v : Source48Vector,
      FCP.BFSSS1V31.sourceSpin48VectorAction s v = v) :
    ∀ v : Source48Vector,
      CliffordAlgebra.contractLeft (Q.polarBilin v) (s : C) = 0 := by
  have hcomm :=
    (FCP.BFSSS1V52K1A.originalSourceSpin48_trivialAction_iff_generator_commutes s).1 hs
  intro v
  have heven : (s : C) ∈ CliffordAlgebra.even Q :=
    spinGroup.mem_even s.property
  have hc :=
    originalSourceClifford_evenCommutator_eq_polarContraction v (s : C) heven
  rw [(hcomm v).symm, sub_self] at hc
  exact hc.symm

#print axioms originalSourceClifford_gradedCommutator_eq_polarContraction
#print axioms originalSourceClifford_evenCommutator_eq_polarContraction
#print axioms originalSourceSpin48_trivialAction_polarContractions_zero

end
end FCP.BFSSS1V52K1C
