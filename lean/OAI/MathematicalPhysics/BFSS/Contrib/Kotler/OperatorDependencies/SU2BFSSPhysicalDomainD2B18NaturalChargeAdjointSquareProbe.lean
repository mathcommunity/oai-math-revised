import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainD2B17TruePhysicalChargeAdjointProbe
import Mathlib.LinearAlgebra.LinearPMap

/-!
# BFSS SU2 D2B18 — exact natural domain of the physical adjoint-square

PROSPECTIVE until pinned Actions compilation and permitted-axiom smoke PASS.

The source charge column T : G.physicalSpace → SourceChargeHilbertOutput
is closed and densely defined by D2B17. Its true Hilbert adjoint T†
is therefore available. The algebraic operator T†T is meaningful ONLY
on {ψ ∈ dom T | Tψ ∈ dom T†}. The ordinary Mathlib LinearPMap.comp
requires the generally false stronger condition T(dom T) ⊆ dom T†.

The natural-domain construction below is adapted, with attribution, from:
Keisuke Suzuki, QuantumSystem/ForMathlib/LinearAlgebra/LinearPMap.lean
and QuantumSystem/Analysis/UnboundedOperator/VonNeumann.lean,
Git commit a2bb99fcb82c820f040004a2f99c875575c72efd (Apache-2.0).
That upstream project currently uses Lean 4.35.0-rc2, not our pinned
Lean 4.34.1; its results are NOT imported, assumed, or claimed to
have passed in our environment. We recheck this small source-derived
construction in the original exact pinned BFSS gate.

Not yet claimed: self-adjointness, form-representation theorem,
manuscript Hamiltonian identification, spectra, or new physical evidence.
-/

namespace FCP.BFSSSU2PhysicalDomainD2B18
noncomputable section

open OAI
open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainD2B17

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
noncomputable def sourcePhysicalChargeAdjointSquare :
    G.physicalSpace →ₗ.[ℂ] G.physicalSpace :=
  naturalComp (sourceOriginalPhysicalChargeAdjoint M G)
    (sourcePhysicalHilbertChargeColumn M G)

/-- No unverified full-domain invariance hypothesis is introduced. -/
theorem sourcePhysicalChargeAdjointSquare_domain (ψ : G.physicalSpace) :
    ψ ∈ (sourcePhysicalChargeAdjointSquare M G).domain ↔
      ∃ hψ : ψ ∈ (sourcePhysicalHilbertChargeColumn M G).domain,
        sourcePhysicalHilbertChargeColumn M G ⟨ψ, hψ⟩ ∈
          (sourceOriginalPhysicalChargeAdjoint M G).domain :=
  naturalComp_mem_domain

/-- The adjoint-square applies the *actual* source Hilbert adjoint
to the source charge column, on its correct natural domain. -/
theorem sourcePhysicalChargeAdjointSquare_apply
    (ψ : (sourcePhysicalChargeAdjointSquare M G).domain) :
    sourcePhysicalChargeAdjointSquare M G ψ =
      sourceOriginalPhysicalChargeAdjoint M G
        ⟨sourcePhysicalHilbertChargeColumn M G
          ⟨ψ, naturalComp_domain_le ψ.property⟩,
          naturalComp_apply_mem ψ⟩ :=
  naturalComp_apply ψ

#print axioms naturalComp_domain
#print axioms naturalComp_mem_domain
#print axioms naturalComp_domain_le
#print axioms naturalComp_apply_mem
#print axioms naturalComp_apply
#print axioms sourcePhysicalChargeAdjointSquare_domain
#print axioms sourcePhysicalChargeAdjointSquare_apply

end
end FCP.BFSSSU2PhysicalDomainD2B18
