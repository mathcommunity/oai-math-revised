import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4K10ASourceClosedJointChargeGraphProbe
import OAI.MathematicalPhysics.BFSS.CovariantFields

/-!
# BFSS SU(2) physical-domain D3A: source kinetic gauge contraction

PROSPECTIVE / UNCOMPILED until the exact GitHub Actions gate succeeds.

The core mathematical issue is invariant contraction of a genuinely
orthonormal spatial/color basis under the source SU(N) gauge isometry.
The abstract lemma has *fully visible* hypotheses and is instantiated
with the original source kinetic symbol and Fréchet derivatives; it
cannot mask a physical assumption.

D3A does not yet assert that the complete supercharge preserves the
gauge-invariant physical L² space; the potential+core assembly is D3B.
-/

namespace FCP.BFSSSU2PhysicalDomainD3A
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open Finset

/-- Contract a linear operator-valued symbol against a linear derivative
in a finite orthonormal basis. Changing that basis by a genuine real
linear isometry preserves the contraction. Nothing physical is assumed. -/
private theorem orthogonalKineticContraction
    {ι E F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : OrthonormalBasis ι ℝ E)
    (U : E ≃ₗᵢ[ℝ] E)
    (K : E →ₗ[ℝ] (F →L[ℝ] F))
    (D : E →L[ℝ] F) :
    (∑ i : ι, K (U (b i)) (D (U (b i)))) =
      ∑ i : ι, K (b i) (D (b i)) := by
  classical
  let c : ι → ι → ℝ := fun i j => inner ℝ (b j) (U (b i))
  have hexpand (i : ι) :
      U (b i) = ∑ j : ι, c i j • b j := by
    simpa only [c] using (b.sum_repr' (U (b i))).symm
  have horth (j k : ι) :
      (∑ i : ι, c i j * c i k) = if j = k then (1 : ℝ) else 0 := by
    calc
      (∑ i : ι, c i j * c i k) =
          ∑ i : ι, inner ℝ (b j) ((b.map U) i) *
            inner ℝ ((b.map U) i) (b k) := by
              apply Finset.sum_congr rfl
              intro i _
              simp only [c, OrthonormalBasis.map_apply]
              rw [real_inner_comm (b k) (U (b i))]
      _ = inner ℝ (b j) (b k) := (b.map U).sum_inner_mul_inner (b j) (b k)
      _ = if j = k then 1 else 0 := b.inner_eq_ite j k
  calc
    (∑ i : ι, K (U (b i)) (D (U (b i)))) =
        ∑ i : ι, ∑ j : ι, ∑ k : ι,
          (c i j * c i k) • K (b j) (D (b k)) := by
            apply Finset.sum_congr rfl
            intro i _
            -- The first rewrite replaces both occurrences of U (b i)
            -- within the entire LHS; a second rewrite has no target.
            conv_lhs => rw [hexpand i]
            simp only [map_sum, map_smul, _root_.sum_apply,
              ContinuousLinearMap.smul_apply, smul_sum, smul_smul]
            conv_lhs => rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            rw [mul_comm (c i k) (c i j)]
    _ = ∑ j : ι, ∑ k : ι, (∑ i : ι, c i j * c i k) •
          K (b j) (D (b k)) := by
            calc
              (∑ i : ι, ∑ j : ι, ∑ k : ι,
                (c i j * c i k) • K (b j) (D (b k))) =
                  ∑ j : ι, ∑ i : ι, ∑ k : ι,
                    (c i j * c i k) • K (b j) (D (b k)) := Finset.sum_comm
              _ = ∑ j : ι, ∑ k : ι, ∑ i : ι,
                    (c i j * c i k) • K (b j) (D (b k)) := by
                      apply Finset.sum_congr rfl
                      intro j _
                      exact Finset.sum_comm
              _ = ∑ j : ι, ∑ k : ι, (∑ i : ι, c i j * c i k) •
                    K (b j) (D (b k)) := by
                      simp only [← Finset.sum_smul]
    _ = ∑ j : ι, ∑ k : ι, (if j = k then (1 : ℝ) else 0) •
          K (b j) (D (b k)) := by
            simp_rw [horth]
    _ = ∑ j : ι, K (b j) (D (b j)) := by
          simp

/-- Real orthogonal invariance for the PINNED BFSS source kinetic symbol
and the Fréchet derivative of any true original smooth-core section. -/
theorem sourceKineticSkewContraction_basisInvariant
    {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)
    (α : SpinIndex) (f : SmoothCore N) (x : Boson N)
    (g : GaugeGroup N) :
    (∑ p : SpaceIndex × ColorIndex N,
      M.kineticSkewLinear α (G.boson g (EuclideanSpace.single p 1))
        (fderiv ℝ (f : Boson N → Fermion N) x
          (G.boson g (EuclideanSpace.single p 1)))) =
    ∑ p : SpaceIndex × ColorIndex N,
      M.kineticSkewLinear α (EuclideanSpace.single p 1)
        (fderiv ℝ (f : Boson N → Fermion N) x
          (EuclideanSpace.single p 1)) := by
  classical
  simpa only [EuclideanSpace.basisFun_apply] using
    orthogonalKineticContraction
      (EuclideanSpace.basisFun (SpaceIndex × ColorIndex N) ℝ)
      (G.boson g) (M.kineticSkewLinear α)
      (fderiv ℝ (f : Boson N → Fermion N) x)

/-- Genuine SU(N)-gauge covariance of the entire contracted original
kinetic symbol and derivative, for each source physical smooth section.
This uses both the pinned G.invariantCore_fderiv and the original
M.kineticSkewLinear_covariant, not simply potential covariance. -/
theorem sourceContractedKinetic_gaugeCovariant
    {N : ℕ} (M : AlgebraData N) (G : M.GaugeData)
    (α : SpinIndex) (f : G.invariantCore)
    (g : GaugeGroup N) (x : Boson N) :
    (∑ p : SpaceIndex × ColorIndex N,
      M.kineticSkewLinear α (EuclideanSpace.single p 1)
        (fderiv ℝ (f.val : Boson N → Fermion N) (G.boson g x)
          (EuclideanSpace.single p 1))) =
      G.fermion g (∑ p : SpaceIndex × ColorIndex N,
        M.kineticSkewLinear α (EuclideanSpace.single p 1)
          (fderiv ℝ (f.val : Boson N → Fermion N) x
            (EuclideanSpace.single p 1))) := by
  let e (p : SpaceIndex × ColorIndex N) : Boson N :=
    EuclideanSpace.single p 1
  calc
    (∑ p : SpaceIndex × ColorIndex N,
      M.kineticSkewLinear α (e p)
        (fderiv ℝ (f.val : Boson N → Fermion N) (G.boson g x) (e p))) =
      ∑ p : SpaceIndex × ColorIndex N,
        M.kineticSkewLinear α (G.boson g (e p))
          (fderiv ℝ (f.val : Boson N → Fermion N) (G.boson g x)
            (G.boson g (e p))) := by
              exact (sourceKineticSkewContraction_basisInvariant M G α
                f.val (G.boson g x) g).symm
    _ = ∑ p : SpaceIndex × ColorIndex N,
          M.kineticSkewLinear α (G.boson g (e p))
            (G.fermion g
              (fderiv ℝ (f.val : Boson N → Fermion N) x (e p))) := by
                apply Finset.sum_congr rfl
                intro p _
                rw [G.invariantCore_fderiv f g x (e p)]
    _ = ∑ p : SpaceIndex × ColorIndex N,
          G.fermion g (M.kineticSkewLinear α (e p)
            (fderiv ℝ (f.val : Boson N → Fermion N) x (e p))) := by
                apply Finset.sum_congr rfl
                intro p _
                exact (G.kineticSkewLinear_covariant g α (e p)
                  (fderiv ℝ (f.val : Boson N → Fermion N) x (e p))).symm
    _ = G.fermion g (∑ p : SpaceIndex × ColorIndex N,
          M.kineticSkewLinear α (e p)
            (fderiv ℝ (f.val : Boson N → Fermion N) x (e p))) := by
              rw [map_sum]

#print axioms sourceKineticSkewContraction_basisInvariant
#print axioms sourceContractedKinetic_gaugeCovariant

end
end FCP.BFSSSU2PhysicalDomainD3A
