import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G7SActualInvariantSmoothCoreInfinitesimalGaussProbe

/-!
L6G7T — the full original SU(2) COLOR-LIE Gauss equation on the
genuine source-defined invariant SmoothCore, for an ARBITRARY original
ColorVector 2 (not merely one of the three fixed color directions).

The source gaugeTangent is a real-linear map in w and the already
qualified original fermion current is a finite REAL-linear color
combination of original fixed-color bounded generators. Applying the
native EuclideanSpace canonical orthonormal basis expansion to the
accepted L6G7S 3-direction equation yields the full Lie-algebra law.

This is a pointwise finite-dimensional smooth-core identity. The
fermionic generator is the original source 48-theta bounded current.
This does not infer differentiability of an unbounded FullL2 operator,
self-adjointness, or any spectral statement.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace FCP.BFSSSU2PhysicalDomainL6G7T
noncomputable section
open scoped BigOperators

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2GaugeG4J
open FCP.BFSSSU2PhysicalDomainL6G6K
open FCP.BFSSSU2PhysicalDomainL6G7S

/-- Source-exact Gauss-law constraint for ALL color Lie directions.
The sign uses the genuine original (-i) source gaugeTangent and the
genuine (+i) Fock gauge-curve generator, related in L6G7Q.
Every state comes from the actual pairedGaugeData.invariantCore. -/
theorem actualInvariantCore_fullColorLieGauss_zero
    (w : ColorVector 2) (f : pairedGaugeData.invariantCore)
    (x : Boson 2) :
    (-(fderiv ℝ (f.val : Boson 2 → Fermion 2) x
        (pairedAlgebraData.gaugeTangent x w)) -
      ∑ c : ColorIndex 2, (w c) •
        (sourceFiberFermionColorGenerator pairedAlgebraData c (f.val x))) = 0 := by
  have hw :
      (∑ c : ColorIndex 2,
        (w c) • EuclideanSpace.single c (1 : ℝ)) = w := by
    simpa only [EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (ColorIndex 2) ℝ).sum_repr w
  have htan :
      pairedAlgebraData.gaugeTangent x w =
        ∑ c : ColorIndex 2, (w c) •
          pairedAlgebraData.gaugeTangent x
            (EuclideanSpace.single c (1 : ℝ)) := by
    calc
      _ = pairedAlgebraData.gaugeTangent x
            (∑ c : ColorIndex 2,
              (w c) • EuclideanSpace.single c (1 : ℝ)) := by rw [hw]
      _ = _ := by rw [map_sum]; simp only [map_smul]
  have hdf :
      fderiv ℝ (f.val : Boson 2 → Fermion 2) x
        (pairedAlgebraData.gaugeTangent x w) =
        ∑ c : ColorIndex 2, (w c) •
          (fderiv ℝ (f.val : Boson 2 → Fermion 2) x
            (pairedAlgebraData.gaugeTangent x
              (EuclideanSpace.single c (1 : ℝ)))) := by
    rw [htan, map_sum]
    simp only [map_smul]
  have hsum :
      (∑ c : ColorIndex 2, (w c) •
        (-(fderiv ℝ (f.val : Boson 2 → Fermion 2) x
          (pairedAlgebraData.gaugeTangent x
            (EuclideanSpace.single c (1 : ℝ)))) -
         sourceFiberFermionColorGenerator pairedAlgebraData c (f.val x))) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    rw [actualInvariantCore_originalSignedGaussDefect_zero c f x]
    simp
  rw [hdf]
  simpa only [smul_sub, smul_neg, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib] using hsum

#print axioms actualInvariantCore_fullColorLieGauss_zero
#check @actualInvariantCore_fullColorLieGauss_zero

end
end FCP.BFSSSU2PhysicalDomainL6G7T
