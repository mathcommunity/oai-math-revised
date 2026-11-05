import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B26WeakFormAssociatedOperatorProbe
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# BFSS SU(2) D2B27 — exact 1/16 normalized weak-form Hamiltonian is self-adjoint

PROSPECTIVE until exact pinned Lean 4.34.1 kernel/axioms gate passes.

D2B21 proves true physical natural-domain A = T†T is self-adjoint.
D2B26 proves the exact closed physical form associated vector condition:
  ∀v∈Dom T, ⟪w,v⟫ = (1/16) ⟪Tu,Tv⟫
  iff u∈Dom A and w=(1/16)A u.
This gate defines the literal partial operator H=(1/16)A, proves true
self-adjointness of H, and identifies its graph with that weak-form condition.

Scalar adjoint proof adapted from the following Apache-2.0 source:
  Physlib/QuantumMechanics/Operators/Unbounded.lean,
  Adam Bornemann and Gregory J. Loges, 2026,
  leanprover-community/physlib @ e411c6e89692e83bc67fe451302ae7f82cf39b10,
  lemmas LinearPMap.adjoint_smul and LinearPMap.IsSelfAdjoint.smul.
  Copyright (c) 2026 Gregory J. Loges.
  Its independently mirrored and verified extraction is in
  rainwangphy/aftd-platform @ 7493428c4d53c9daa50695e401c3d601c1cf5ee6.
We adapt the proof to the original source-pinned Mathlib 4.34.1,
WITHOUT importing Physlib or assuming any theorem from it.

Unproved beyond this file: literal manuscript gauge/Spin(48) realization
unitary intertwiner, the published positive eigenvalue spectral theorem,
or any empirical framework reclassification.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B27
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B17
open FCP.BFSSSU2PhysicalDomainD2B18
open FCP.BFSSSU2PhysicalDomainD2B21
open FCP.BFSSSU2PhysicalDomainD2B26
open LinearPMap
open scoped ComplexConjugate

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Exact adjoint of nonzero-scaled densely defined partial operator,
proved in our frozen Mathlib without an external dependency. -/
theorem adjoint_smul_of_dense (U : E →ₗ.[ℂ] F)
    (hd : Dense (U.domain : Set E)) {c : ℂ} (hc : c ≠ 0) :
    (c • U).adjoint = (starRingEnd ℂ) c • U.adjoint := by
  refine LinearPMap.dExt ?_ fun x y hxy => ?_
  · ext x
    change Continuous (fun w => inner ℂ x (c • U w)) ↔
      Continuous (fun w => inner ℂ x (U w))
    exact Iff.trans (by simp [inner_smul_right])
      (continuous_const_smul_iff₀ hc)
  · refine LinearPMap.adjoint_apply_eq
      (by simpa only [LinearPMap.smul_domain] using hd) x fun w => ?_
    simp [inner_smul_left, inner_smul_right,
      LinearPMap.adjoint_isFormalAdjoint hd y w, hxy]

/-- Scalar multiplication by any nonzero REAL complex scalar
preserves genuine self-adjointness, including the domain equality. -/
theorem selfAdjoint_smul_real (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) {c : ℂ}
    (hc : c ≠ 0) (hr : (starRingEnd ℂ) c = c) :
    IsSelfAdjoint (c • A) := by
  change (c • A).adjoint = c • A
  rw [adjoint_smul_of_dense A hA.dense_domain hc,
    hr, LinearPMap.isSelfAdjoint_def.mp hA]

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The actual NORMALIZED physical source BFSS Hamiltonian,
on exactly the natural domain of T†T, no artificial extension. -/
noncomputable def sourcePhysicalNormalizedHamiltonian :
    G.physicalSpace →ₗ.[ℂ] G.physicalSpace :=
  (1 / 16 : ℂ) • sourcePhysicalChargeAdjointSquare M G

/-- The scalar normalization changes NONE of the source-domain points. -/
theorem sourcePhysicalNormalizedHamiltonian_domain :
    (sourcePhysicalNormalizedHamiltonian M G).domain =
      (sourcePhysicalChargeAdjointSquare M G).domain := by
  rfl

/-- The actual Hamiltonian action on the original natural domain. -/
theorem sourcePhysicalNormalizedHamiltonian_apply
    (u : (sourcePhysicalChargeAdjointSquare M G).domain) :
    sourcePhysicalNormalizedHamiltonian M G
      ⟨u, by rw [sourcePhysicalNormalizedHamiltonian_domain M G]; exact u.property⟩ =
        (1 / 16 : ℂ) • sourcePhysicalChargeAdjointSquare M G u := by
  rfl

/-- GENUINE self-adjointness of the normalized original source
physical Hamiltonian—not just formal symmetry. -/
theorem sourcePhysicalNormalizedHamiltonian_selfAdjoint :
    letI : CompleteSpace G.physicalSpace :=
      sourceOriginalPhysicalHilbert_complete M G
    IsSelfAdjoint (sourcePhysicalNormalizedHamiltonian M G) := by
  let : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  apply selfAdjoint_smul_real (sourcePhysicalChargeAdjointSquare M G)
    (sourcePhysicalChargeAdjointSquare_selfAdjoint M G)
    (by norm_num)
  simp only [map_div₀, map_one, map_ofNat]

/-- The weak-form representing-vector equation selects exactly
this very normalized source Hamiltonian, including its domain. -/
theorem sourcePhysicalNormalizedHamiltonian_weakForm_iff
    (u : (sourcePhysicalHilbertChargeColumn M G).domain)
    (w : G.physicalSpace) :
    (∀ v : (sourcePhysicalHilbertChargeColumn M G).domain,
      inner ℂ w (v : G.physicalSpace) =
        (1 / 16 : ℂ) *
          inner ℂ (sourcePhysicalHilbertChargeColumn M G u)
            (sourcePhysicalHilbertChargeColumn M G v)) ↔
      ∃ h : (u : G.physicalSpace) ∈
          (sourcePhysicalNormalizedHamiltonian M G).domain,
        w = sourcePhysicalNormalizedHamiltonian M G ⟨u, h⟩ := by
  exact sourcePhysicalNormalizedWeakForm_associatedOperator_iff M G u w

theorem sourcePhysicalNormalizedHamiltonian_closed :
    (sourcePhysicalNormalizedHamiltonian M G).IsClosed := by
  let : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  exact (sourcePhysicalNormalizedHamiltonian_selfAdjoint M G).isClosed

theorem sourcePhysicalNormalizedHamiltonian_domain_dense :
    Dense ((sourcePhysicalNormalizedHamiltonian M G).domain :
      Set G.physicalSpace) := by
  let : CompleteSpace G.physicalSpace :=
    sourceOriginalPhysicalHilbert_complete M G
  exact (sourcePhysicalNormalizedHamiltonian_selfAdjoint M G).dense_domain

#print axioms adjoint_smul_of_dense
#print axioms selfAdjoint_smul_real
#print axioms sourcePhysicalNormalizedHamiltonian_domain
#print axioms sourcePhysicalNormalizedHamiltonian_apply
#print axioms sourcePhysicalNormalizedHamiltonian_selfAdjoint
#print axioms sourcePhysicalNormalizedHamiltonian_weakForm_iff
#print axioms sourcePhysicalNormalizedHamiltonian_closed
#print axioms sourcePhysicalNormalizedHamiltonian_domain_dense

end
end FCP.BFSSSU2PhysicalDomainD2B27
