import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainS1DRelativeGaugeCharacterProbe
import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6G6XOriginalSU2GaugeCurveProbe

/-!
# S1E: algebraic reduction of the ACTUAL source relative gauge character

Strict candidate, NOT qualified before a complete Lean and axiom gate.
Given the exact source S1D scalar and source positive-i gauge curves,
the character is trivial IF four concrete, separately dischargeable
matrix identities hold: inverse-conjugacy and parameter-halving for
the original Z and Y curves, plus source Euler generation.

This gate does NOT assert those curve hypotheses automatically,
construct the manuscript's independent Spin(48) implementer,
or prove an independent spectral assertion.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace FCP.BFSSSU2PhysicalDomainS1E
noncomputable section

open OAI.BFSSQuantum
open FCP.BFSSSU2GaugeG1A
open FCP.BFSSSU2PhysicalDomainS1D
open FCP.BFSSSU2PhysicalDomainL6G6X

/-- Conjugation invariance follows from multiplicativity into
the actual commutative field, without assuming continuity or
nonvanishing as an extra hypothesis. -/
theorem scalar_character_conjugation_invariant
    {G : Type*} [Group G]
    (chi : G → ℂ)
    (hone : chi 1 = 1)
    (hmul : ∀ g h : G, chi (g * h) = chi g * chi h)
    (g k : G) :
    chi (k * g * k⁻¹) = chi g := by
  have hcancel : chi k * chi k⁻¹ = 1 := by
    calc
      chi k * chi k⁻¹ = chi (k * k⁻¹) := (hmul k k⁻¹).symm
      _ = chi 1 := by rw [mul_inv_cancel]
      _ = 1 := hone
  calc
    chi (k * g * k⁻¹) = chi k * chi g * chi k⁻¹ := by
      rw [hmul (k * g) k⁻¹, hmul k g]
    _ = chi g * (chi k * chi k⁻¹) := by ring
    _ = chi g := by rw [hcancel]; ring

/-- If every element of a rooted one-parameter family is conjugate
to its inverse, an abelian scalar character is trivial on the family.
The square root is the *same original parameter family*, not an
extra group-theoretic assumption about arbitrary SU(2) elements. -/
theorem scalar_character_rooted_curve_trivial
    {G : Type*} [Group G]
    (chi : G → ℂ)
    (hone : chi 1 = 1)
    (hmul : ∀ g h : G, chi (g * h) = chi g * chi h)
    (curve : ℝ → G)
    (hflip : ∀ t : ℝ, ∃ k : G,
      k * curve t * k⁻¹ = (curve t)⁻¹)
    (hhalf : ∀ t : ℝ,
      curve (t / 2) * curve (t / 2) = curve t)
    (t : ℝ) :
    chi (curve t) = 1 := by
  have hsquare (u : ℝ) : chi (curve u) * chi (curve u) = 1 := by
    obtain ⟨k, hk⟩ := hflip u
    have hinv : chi (curve u) = chi ((curve u)⁻¹) := by
      calc
        chi (curve u) = chi (k * curve u * k⁻¹) :=
          (scalar_character_conjugation_invariant chi hone hmul (curve u) k).symm
        _ = chi ((curve u)⁻¹) := congrArg chi hk
    calc
      chi (curve u) * chi (curve u) =
          chi (curve u) * chi ((curve u)⁻¹) :=
            congrArg (fun z : ℂ => chi (curve u) * z) hinv
      _ = chi (curve u * (curve u)⁻¹) := (hmul _ _).symm
      _ = 1 := by simpa only [mul_inv_cancel] using hone
  calc
    chi (curve t) = chi (curve (t / 2) * curve (t / 2)) :=
      congrArg chi (hhalf t).symm
    _ = chi (curve (t / 2)) * chi (curve (t / 2)) := hmul _ _
    _ = 1 := hsquare (t / 2)

/-- Algebraic source SU(2) Euler reduction. ALL concrete hypotheses
stay visible. This theorem makes no hidden claim that matrix
conjugacies or half-parameter laws have already been Lean-qualified. -/
theorem scalar_character_trivial_of_zyz
    {G : Type*} [Group G]
    (chi : G → ℂ)
    (hone : chi 1 = 1)
    (hmul : ∀ g h : G, chi (g * h) = chi g * chi h)
    (zcurve ycurve : ℝ → G)
    (hzflip : ∀ t : ℝ, ∃ k : G,
      k * zcurve t * k⁻¹ = (zcurve t)⁻¹)
    (hyflip : ∀ t : ℝ, ∃ k : G,
      k * ycurve t * k⁻¹ = (ycurve t)⁻¹)
    (hzhalf : ∀ t : ℝ,
      zcurve (t / 2) * zcurve (t / 2) = zcurve t)
    (hyhalf : ∀ t : ℝ,
      ycurve (t / 2) * ycurve (t / 2) = ycurve t)
    (heuler : ∀ g : G, ∃ a b c : ℝ,
      zcurve a * ycurve b * zcurve c = g)
    (g : G) : chi g = 1 := by
  obtain ⟨a, b, c, hg⟩ := heuler g
  calc
    chi g = chi (zcurve a * ycurve b * zcurve c) :=
      congrArg chi hg.symm
    _ = chi (zcurve a) * chi (ycurve b) * chi (zcurve c) := by
      rw [hmul (zcurve a * ycurve b) (zcurve c),
          hmul (zcurve a) (ycurve b)]
    _ = 1 := by
      rw [scalar_character_rooted_curve_trivial chi hone hmul
            zcurve hzflip hzhalf a,
          scalar_character_rooted_curve_trivial chi hone hmul
            ycurve hyflip hyhalf b,
          scalar_character_rooted_curve_trivial chi hone hmul
            zcurve hzflip hzhalf c]
      ring

/-- Literal original +i Pauli curve (not a surrogate subgroup). -/
noncomputable def sourceZ (t : ℝ) : GaugeGroup 2 :=
  sourcePlusIGaugeCurve (2 : Fin 3) t

/-- Literal original +i Pauli curve (not a surrogate subgroup). -/
noncomputable def sourceY (t : ℝ) : GaugeGroup 2 :=
  sourcePlusIGaugeCurve (1 : Fin 3) t

/-- S1D's actual 48-Majorana source relative character is identically
one, CONDITIONAL ONLY on the four exact curve identities and Euler
factorization. The hypotheses are NOT yet discharged in this gate. -/
theorem original_relativeGaugeScalar_one_of_curve_relations
    (V : GaugeGroup 2 →* (Fermion 2 ≃ₗ[ℂ] Fermion 2))
    (hV : ∀ (g : GaugeGroup 2) (α : SpinIndex)
      (A : ColorIndex 2) (v : Fermion 2),
      V g (pairedTheta α A v) =
        ∑ B : ColorIndex 2,
          (pairedAlgebraData.adjointCoefficient g A B : ℂ) •
            pairedTheta α B (V g v))
    (hzflip : ∀ t : ℝ, ∃ k : GaugeGroup 2,
      k * sourceZ t * k⁻¹ = (sourceZ t)⁻¹)
    (hyflip : ∀ t : ℝ, ∃ k : GaugeGroup 2,
      k * sourceY t * k⁻¹ = (sourceY t)⁻¹)
    (hzhalf : ∀ t : ℝ,
      sourceZ (t / 2) * sourceZ (t / 2) = sourceZ t)
    (hyhalf : ∀ t : ℝ,
      sourceY (t / 2) * sourceY (t / 2) = sourceY t)
    (heuler : ∀ g : GaugeGroup 2, ∃ a b c : ℝ,
      sourceZ a * sourceY b * sourceZ c = g)
    (g : GaugeGroup 2) :
    relativeGaugeScalar V hV g = 1 := by
  exact scalar_character_trivial_of_zyz
    (relativeGaugeScalar V hV)
    (relativeGaugeScalar_one V hV)
    (relativeGaugeScalar_mul V hV)
    sourceZ sourceY hzflip hyflip hzhalf hyhalf heuler g

#print axioms scalar_character_conjugation_invariant
#print axioms scalar_character_rooted_curve_trivial
#print axioms scalar_character_trivial_of_zyz
#print axioms sourceZ
#print axioms sourceY
#print axioms original_relativeGaugeScalar_one_of_curve_relations

end
end FCP.BFSSSU2PhysicalDomainS1E
