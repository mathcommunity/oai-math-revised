import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H5E8BBOriginalPhysicalHilbertChargeAdjointProbe
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# H5E8BC — original SU2 physical Hilbert sixteen-charge NATURAL adjoint square

PROSPECTIVE / NOT QUALIFIED until pinned Lean kernel + exact axiom gate PASS.

Exactly the original source AY/BA/BB charge T and genuine BB Hilbert
adjoint T† are used. We do NOT import old D2B17–19 deformed-source
modules or assume two distinct closed operators are identical.

The natural-domain operator T†T exists only for ψ∈Dom(T) with
Tψ∈Dom(T†). No false entire-domain invariance of T is assumed.
On its true natural domain, the real energy is ‖Tψ‖² and
T†T is formally symmetric and nonnegative. Formal symmetry does
NOT prove self-adjointness or Hamiltonian identification.

The generic naturalComp and formal-product proofs are locally adapted,
not imported or newly assumed, from the accepted FCP D2B18/D2B19 source.
Historical attribution: Keisuke Suzuki, QuantumSystem,
ForMathlib/LinearAlgebra/LinearPMap.lean and
Analysis/UnboundedOperator/VonNeumann.lean,
commit a2bb99fcb82c820f040004a2f99c875575c72efd (Apache-2.0).

Manuscript Clifford/Spin(48) identification, exact normalized associated
Hamiltonian, Spin(9) sector reduction and positive spectrum remain OPEN.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainL6H5E8BC
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6H5E8AY
open FCP.BFSSSU2PhysicalDomainL6H5E8BA
open FCP.BFSSSU2PhysicalDomainL6H5E8BB
open RCLike
open scoped ComplexConjugate

section NaturalDomain

variable {E F K : Type*}
variable [AddCommGroup E] [Module ℂ E]
variable [AddCommGroup F] [Module ℂ F]
variable [AddCommGroup K] [Module ℂ K]

/-- The natural, two-layer domain: x in dom f and f(x) in dom g. -/
def naturalCompDomain (g : F →ₗ.[ℂ] K) (f : E →ₗ.[ℂ] F) :
    Submodule ℂ E :=
  (g.domain.comap f.toFun).map f.domain.subtype

private theorem naturalCompDomain_le (g : F →ₗ.[ℂ] K)
    (f : E →ₗ.[ℂ] F) : naturalCompDomain g f ≤ f.domain := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

/-- Source-derived composition without a false full-domain invariance hypothesis. -/
def naturalComp (g : F →ₗ.[ℂ] K) (f : E →ₗ.[ℂ] F) : E →ₗ.[ℂ] K :=
  g.comp (f.domRestrict (naturalCompDomain g f)) fun x => by
    obtain ⟨y, hy, hyx⟩ := x.2.1
    rw [LinearPMap.domRestrict_apply (hyx.symm : (x : E) = y)]
    exact hy

theorem naturalComp_domain (g : F →ₗ.[ℂ] K) (f : E →ₗ.[ℂ] F) :
    (naturalComp g f).domain = naturalCompDomain g f :=
  inf_eq_left.mpr (naturalCompDomain_le g f)

theorem naturalComp_mem_domain {g : F →ₗ.[ℂ] K}
    {f : E →ₗ.[ℂ] F} {x : E} :
    x ∈ (naturalComp g f).domain ↔
      ∃ hx : x ∈ f.domain, f ⟨x, hx⟩ ∈ g.domain := by
  refine ⟨fun h => ⟨h.2, ?_⟩, fun ⟨hx, h⟩ => ⟨⟨⟨x, hx⟩, h, rfl⟩, hx⟩⟩
  obtain ⟨y, hy, hyx⟩ := h.1
  obtain rfl : y = ⟨x, h.2⟩ := Subtype.ext hyx
  exact hy

theorem naturalComp_domain_le {g : F →ₗ.[ℂ] K}
    {f : E →ₗ.[ℂ] F} : (naturalComp g f).domain ≤ f.domain :=
  fun _ h => h.2

theorem naturalComp_apply_mem {g : F →ₗ.[ℂ] K}
    {f : E →ₗ.[ℂ] F} (x : (naturalComp g f).domain) :
    f ⟨x, naturalComp_domain_le x.property⟩ ∈ g.domain :=
  (naturalComp_mem_domain.mp x.property).2

theorem naturalComp_apply {g : F →ₗ.[ℂ] K}
    {f : E →ₗ.[ℂ] F} (x : (naturalComp g f).domain) :
    naturalComp g f x =
      g ⟨f ⟨x, naturalComp_domain_le x.property⟩,
        naturalComp_apply_mem x⟩ :=
  rfl

end NaturalDomain

variable (M : AlgebraData 2) (G : M.GaugeData)

/-- The exact natural-domain adjoint-square of the ORIGINAL source
physical Hilbert charge column. This is a genuine Mathlib LinearPMap,
but self-adjointness and Hamiltonian identification are later obligations. -/
noncomputable def originalMinimalPhysicalHilbertChargeAdjointSquare :
    G.physicalSpace →ₗ.[ℂ] G.physicalSpace :=
  naturalComp (originalMinimalPhysicalHilbertChargeAdjoint M G)
    (originalMinimalPhysicalHilbertChargeColumn M G)

/-- No unverified full-domain invariance hypothesis is introduced. -/
theorem originalMinimalPhysicalHilbertChargeAdjointSquare_domain (ψ : G.physicalSpace) :
    ψ ∈ (originalMinimalPhysicalHilbertChargeAdjointSquare M G).domain ↔
      ∃ hψ : ψ ∈ (originalMinimalPhysicalHilbertChargeColumn M G).domain,
        originalMinimalPhysicalHilbertChargeColumn M G ⟨ψ, hψ⟩ ∈
          (originalMinimalPhysicalHilbertChargeAdjoint M G).domain :=
  naturalComp_mem_domain

/-- The adjoint-square applies the *actual* source Hilbert adjoint
to the source charge column, on its correct natural domain. -/
theorem originalMinimalPhysicalHilbertChargeAdjointSquare_apply
    (ψ : (originalMinimalPhysicalHilbertChargeAdjointSquare M G).domain) :
    originalMinimalPhysicalHilbertChargeAdjointSquare M G ψ =
      originalMinimalPhysicalHilbertChargeAdjoint M G
        ⟨originalMinimalPhysicalHilbertChargeColumn M G
          ⟨ψ, naturalComp_domain_le ψ.property⟩,
          naturalComp_apply_mem ψ⟩ :=
  naturalComp_apply ψ



variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Natural-domain adjoint-square Hilbert pairing, using only the
actual formal-adjoint identity and no analytic assumptions on products. -/
theorem naturalFormalProduct_inner
    (T : E →ₗ.[ℂ] F) (A : F →ₗ.[ℂ] E)
    (hA : A.IsFormalAdjoint T)
    (u : (naturalComp A T).domain) :
    inner ℂ (naturalComp A T u) (u : E) =
      inner ℂ (T ⟨u, naturalComp_domain_le u.property⟩)
        (T ⟨u, naturalComp_domain_le u.property⟩) := by
  rw [naturalComp_apply]
  exact hA ⟨_, naturalComp_apply_mem u⟩
    ⟨u, naturalComp_domain_le u.property⟩

/-- The natural product is formally symmetric as a consequence of
the true Hilbert adjoint pairing; this alone is not self-adjointness. -/
theorem naturalFormalProduct_symmetric
    (T : E →ₗ.[ℂ] F) (A : F →ₗ.[ℂ] E)
    (hA : A.IsFormalAdjoint T) :
    (naturalComp A T).IsFormalAdjoint (naturalComp A T) := by
  intro x y
  have h₁ := hA
    (⟨T ⟨x, naturalComp_domain_le x.property⟩, naturalComp_apply_mem x⟩)
    (⟨y, naturalComp_domain_le y.property⟩)
  have h₂ := hA
    (⟨T ⟨y, naturalComp_domain_le y.property⟩, naturalComp_apply_mem y⟩)
    (⟨x, naturalComp_domain_le x.property⟩)
  rw [naturalComp_apply, naturalComp_apply]
  calc
    _ = _ := h₁
    _ = conj _ := (inner_conj_symm _ _).symm
    _ = conj _ := congrArg conj h₂.symm
    _ = _ := inner_conj_symm _ _





theorem originalMinimalPhysicalHilbertChargeAdjointSquare_inner
    (u : (originalMinimalPhysicalHilbertChargeAdjointSquare M G).domain) :
    inner ℂ (originalMinimalPhysicalHilbertChargeAdjointSquare M G u)
      (u : G.physicalSpace) =
      inner ℂ
        (originalMinimalPhysicalHilbertChargeColumn M G
          ⟨u, naturalComp_domain_le u.property⟩)
        (originalMinimalPhysicalHilbertChargeColumn M G
          ⟨u, naturalComp_domain_le u.property⟩) :=
  naturalFormalProduct_inner _ _
    (originalMinimalPhysicalHilbertChargeAdjoint_isFormalAdjoint M G) u

theorem originalMinimalPhysicalHilbertChargeAdjointSquare_symmetric :
    (originalMinimalPhysicalHilbertChargeAdjointSquare M G).IsFormalAdjoint
      (originalMinimalPhysicalHilbertChargeAdjointSquare M G) :=
  naturalFormalProduct_symmetric _ _
    (originalMinimalPhysicalHilbertChargeAdjoint_isFormalAdjoint M G)

/-- The source physical adjoint-square energy is the *exact* squared
sixteen-charge Hilbert norm on its actual natural domain. -/
theorem originalMinimalPhysicalHilbertChargeAdjointSquare_energy
    (u : (originalMinimalPhysicalHilbertChargeAdjointSquare M G).domain) :
    re (inner ℂ (originalMinimalPhysicalHilbertChargeAdjointSquare M G u)
      (u : G.physicalSpace)) =
      ‖originalMinimalPhysicalHilbertChargeColumn M G
        ⟨u, naturalComp_domain_le u.property⟩‖ ^ 2 := by
  rw [originalMinimalPhysicalHilbertChargeAdjointSquare_inner M G u, inner_self_eq_norm_sq]

theorem originalMinimalPhysicalHilbertChargeAdjointSquare_nonneg
    (u : (originalMinimalPhysicalHilbertChargeAdjointSquare M G).domain) :
    0 ≤ re (inner ℂ (originalMinimalPhysicalHilbertChargeAdjointSquare M G u)
      (u : G.physicalSpace)) := by
  rw [originalMinimalPhysicalHilbertChargeAdjointSquare_energy M G u]
  exact sq_nonneg _



#print axioms naturalComp_domain
#print axioms naturalComp_mem_domain
#print axioms naturalComp_domain_le
#print axioms naturalComp_apply_mem
#print axioms naturalComp_apply
#print axioms originalMinimalPhysicalHilbertChargeAdjointSquare_domain
#print axioms originalMinimalPhysicalHilbertChargeAdjointSquare_apply
#print axioms naturalFormalProduct_inner
#print axioms naturalFormalProduct_symmetric
#print axioms originalMinimalPhysicalHilbertChargeAdjointSquare_inner
#print axioms originalMinimalPhysicalHilbertChargeAdjointSquare_symmetric
#print axioms originalMinimalPhysicalHilbertChargeAdjointSquare_energy
#print axioms originalMinimalPhysicalHilbertChargeAdjointSquare_nonneg

end
end FCP.BFSSSU2PhysicalDomainL6H5E8BC
