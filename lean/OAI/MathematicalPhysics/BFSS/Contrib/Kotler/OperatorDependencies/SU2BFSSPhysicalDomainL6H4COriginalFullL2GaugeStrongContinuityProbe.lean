import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSPhysicalDomainL6H4BOriginalFullL2GaugeCoreStrongContinuityProbe

/-!
L6H4C — source-exact original BFSS SU(2) gauge representation:
STRONG norm-topology continuity of ALL orbits in the genuine FullL2 2.

The proof uses only:
* the actual source smooth-core dense range (OAI.BFSSQuantum.coreToL2_dense),
* the source-exact FullL2 gauge isometry (qualified L6G7W),
* independently source-qualified H4B core strong-continuity,
* pinned Mathlib metric triangle/continuity lemmas.

This is an epsilon/3 density extension of the SAME original source
operator, not a surrogate space, altered source action, extra axiom,
or proof of unbounded-generator domain / spectral conclusions.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 170000

namespace FCP.BFSSSU2PhysicalDomainL6H4C
noncomputable section

open OAI.BFSSQuantum
open OAI.BFSSQuantum.AlgebraData
open FCP.BFSSSU2PhysicalDomainL6G7U
open FCP.BFSSSU2PhysicalDomainL6G7W
open FCP.BFSSSU2PhysicalDomainL6H4B
open Filter

/-- Every vector of the genuine original BFSS FullL2 Hilbert space
has a norm-topology continuous SU(2) gauge orbit. The argument
extends the previously qualified source smooth-core statement
through exact source density and group-uniform isometry. -/
theorem actualOriginalFullL2GaugePair_orbit_continuous
    (v : FullL2 2) :
    Continuous (fun g : GaugeGroup 2 =>
      actualOriginalFullL2GaugePairCLM g v) := by
  apply Metric.continuous_iff'.2
  intro h ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨f, hf⟩ :=
    (coreToL2_dense (N := 2)).exists_dist_lt v hthird
  have hcore :
      ∀ᶠ g in nhds h,
        dist (actualOriginalFullL2GaugePairCLM g (coreToL2 f))
          (actualOriginalFullL2GaugePairCLM h (coreToL2 f)) < ε / 3 :=
    (Metric.continuousAt_iff'.1
      ((actualOriginalFullL2GaugeCore_orbit_continuous f).continuousAt (x := h)))
      (ε / 3) hthird
  have htriangle (g : GaugeGroup 2) :
      dist (actualOriginalFullL2GaugePairCLM g v)
        (actualOriginalFullL2GaugePairCLM h v) ≤
        dist v (coreToL2 f) +
        dist (actualOriginalFullL2GaugePairCLM g (coreToL2 f))
          (actualOriginalFullL2GaugePairCLM h (coreToL2 f)) +
        dist (coreToL2 f) v := by
    have hg :
        dist (actualOriginalFullL2GaugePairCLM g v)
          (actualOriginalFullL2GaugePairCLM g (coreToL2 f)) =
          dist v (coreToL2 f) :=
      (actualOriginalFullL2GaugePair_isometry g).dist_eq v (coreToL2 f)
    have hh :
        dist (actualOriginalFullL2GaugePairCLM h (coreToL2 f))
          (actualOriginalFullL2GaugePairCLM h v) =
          dist (coreToL2 f) v :=
      (actualOriginalFullL2GaugePair_isometry h).dist_eq (coreToL2 f) v
    calc
      _ ≤ dist (actualOriginalFullL2GaugePairCLM g v)
              (actualOriginalFullL2GaugePairCLM g (coreToL2 f)) +
            dist (actualOriginalFullL2GaugePairCLM g (coreToL2 f))
              (actualOriginalFullL2GaugePairCLM h (coreToL2 f)) +
            dist (actualOriginalFullL2GaugePairCLM h (coreToL2 f))
              (actualOriginalFullL2GaugePairCLM h v) :=
        dist_triangle4 _ _ _ _
      _ = _ := by rw [hg, hh]
  filter_upwards [hcore] with g hg
  have hf' : dist (coreToL2 f) v < ε / 3 := by
    simpa only [dist_comm] using hf
  exact lt_of_le_of_lt (htriangle g) (by linarith)

#print axioms actualOriginalFullL2GaugePair_orbit_continuous
#check @actualOriginalFullL2GaugePair_orbit_continuous

end
end FCP.BFSSSU2PhysicalDomainL6H4C
