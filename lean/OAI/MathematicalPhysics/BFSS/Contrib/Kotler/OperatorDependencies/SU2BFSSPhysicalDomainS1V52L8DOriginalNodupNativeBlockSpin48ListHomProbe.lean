import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1V52L8COriginalNativeSpin48CrossBlockImageCommutationProbe

/-!
S1V52-L8D — STAGED, UNQUALIFIED abstract finite-list integration
of the original native spin-block homomorphisms.

Under `xs.Nodup` the images of distinct spin blocks commute
by the L8C ORIGINAL native GaugeGroup2→true Spin48 cross-block
lemma. We may then use a deterministic List.prod in the
NONCOMMUTATIVE genuine spinGroup source48Quadratic.

The theorem is parameterized by ANY nodup list of original
RealSpinBlock labels, and proves an actual original native
GaugeGroup 2 →* spinGroup Q map. It avoids falsely declaring
Mathlib Spin48 a commutative monoid, or using Finset.prod.

The final exactly-sixteen-source-block specialization in the
pinned finProdFinEquiv order remains an independent next gate,
as do original pairedLabelEquiv/gauge physical action matching.

This file is research-only until L8B/C are accepted and strict CI
qualifies every root below. No new source SU2 group or axioms.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000

namespace FCP.BFSSS1V52L8D
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSS1V0
open FCP.BFSSS1V5
open FCP.BFSSS1V52L7C7
open FCP.BFSSS1V52L8C

private abbrev Q : QuadraticForm ℝ Source48Vector := source48Quadratic

/-- Ordered product of actual original native per-block Spin48 images,
without inventing a commutative group structure. -/
noncomputable def originalNativeBlockSpinProd
    (xs : List RealSpinBlock) (g : GaugeGroup 2) : spinGroup Q :=
  (xs.map (fun α => originalNativeGaugeSpinHom α g)).prod

/-- Any genuine original native source-spin element in one block
commutes with the entire product from an index list that
does not contain that block. -/
theorem originalNativeBlockSpin_comm_list
    (α : RealSpinBlock) (g h : GaugeGroup 2) :
    ∀ xs : List RealSpinBlock, α ∉ xs →
      originalNativeGaugeSpinHom α g * originalNativeBlockSpinProd xs h =
        originalNativeBlockSpinProd xs h * originalNativeGaugeSpinHom α g := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp [originalNativeBlockSpinProd]
  | cons β xs ih =>
      intro hnot
      have hab : α ≠ β := by
        intro heq
        apply hnot
        simp [heq]
      have htail : α ∉ xs := by
        intro hm
        apply hnot
        simp [hm]
      have hhead :=
        originalNativeSpinHom_crossBlock_comm α β hab g h
      have hrest := ih htail
      change
        originalNativeGaugeSpinHom α g *
          (originalNativeGaugeSpinHom β h *
            originalNativeBlockSpinProd xs h) =
        (originalNativeGaugeSpinHom β h *
            originalNativeBlockSpinProd xs h) *
          originalNativeGaugeSpinHom α g
      calc
        originalNativeGaugeSpinHom α g *
            (originalNativeGaugeSpinHom β h *
              originalNativeBlockSpinProd xs h) =
          (originalNativeGaugeSpinHom α g *
             originalNativeGaugeSpinHom β h) *
            originalNativeBlockSpinProd xs h := by simp only [mul_assoc]
        _ = (originalNativeGaugeSpinHom β h *
             originalNativeGaugeSpinHom α g) *
            originalNativeBlockSpinProd xs h := by rw [hhead]
        _ = originalNativeGaugeSpinHom β h *
            (originalNativeGaugeSpinHom α g *
              originalNativeBlockSpinProd xs h) := by simp only [mul_assoc]
        _ = originalNativeGaugeSpinHom β h *
            (originalNativeBlockSpinProd xs h *
              originalNativeGaugeSpinHom α g) := by rw [hrest]
        _ = (originalNativeGaugeSpinHom β h *
              originalNativeBlockSpinProd xs h) *
             originalNativeGaugeSpinHom α g := by simp only [mul_assoc]

/-- An ordered NO-DUPLICATES product of the actual original
per-spin-block SU2→Spin48 homomorphisms respects multiplication
in genuine original source Spin48. -/
theorem originalNativeBlockSpinProd_mul_of_nodup
    (g h : GaugeGroup 2) :
    ∀ xs : List RealSpinBlock, xs.Nodup →
      originalNativeBlockSpinProd xs (g*h) =
        originalNativeBlockSpinProd xs g *
          originalNativeBlockSpinProd xs h := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp [originalNativeBlockSpinProd]
  | cons α xs ih =>
      intro hnodup
      have hnot : α ∉ xs := (List.nodup_cons.mp hnodup).1
      have htail : xs.Nodup := (List.nodup_cons.mp hnodup).2
      have hprod := ih htail
      have hcross :=
        originalNativeBlockSpin_comm_list α h g xs hnot
      change
        originalNativeGaugeSpinHom α (g*h) *
          originalNativeBlockSpinProd xs (g*h) =
        (originalNativeGaugeSpinHom α g *
          originalNativeBlockSpinProd xs g) *
        (originalNativeGaugeSpinHom α h *
          originalNativeBlockSpinProd xs h)
      rw [map_mul, hprod]
      calc
        (originalNativeGaugeSpinHom α g *
            originalNativeGaugeSpinHom α h) *
          (originalNativeBlockSpinProd xs g *
            originalNativeBlockSpinProd xs h) =
          (originalNativeGaugeSpinHom α g *
            (originalNativeGaugeSpinHom α h *
              originalNativeBlockSpinProd xs g)) *
            originalNativeBlockSpinProd xs h := by simp only [mul_assoc]
        _ = (originalNativeGaugeSpinHom α g *
            (originalNativeBlockSpinProd xs g *
              originalNativeGaugeSpinHom α h)) *
            originalNativeBlockSpinProd xs h := by rw [hcross]
        _ = (originalNativeGaugeSpinHom α g *
              originalNativeBlockSpinProd xs g) *
            (originalNativeGaugeSpinHom α h *
              originalNativeBlockSpinProd xs h) := by simp only [mul_assoc]

/-- Genuine source native SU2→Spin48 hom for any ORIGINAL source
block list with distinct labels, using a noncommutative List.prod.
No independent commutative target-group assumption. -/
noncomputable def originalNativeBlockSpinHom_of_nodup
    (xs : List RealSpinBlock) (hnodup : xs.Nodup) :
    GaugeGroup 2 →* spinGroup Q where
  toFun g := originalNativeBlockSpinProd xs g
  map_one' := by
    simp [originalNativeBlockSpinProd]
  map_mul' g h :=
    originalNativeBlockSpinProd_mul_of_nodup g h xs hnodup

#print axioms originalNativeBlockSpinProd
#print axioms originalNativeBlockSpin_comm_list
#print axioms originalNativeBlockSpinProd_mul_of_nodup
#print axioms originalNativeBlockSpinHom_of_nodup
end
end FCP.BFSSS1V52L8D
