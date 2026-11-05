import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2FermionF2B2MixedDiagProbe

/-!
# BFSS fermions F2-B2c3 — complete real/imaginary mixed Majorana CAR

This short theorem assembles two separately kernel-accepted lemmas:
F2-B2c1 handles all distinct mode pairs, and F2-B2c2 handles
equal mode pairs. No new axiom or physical premise enters the proof.

The 48-label delta-indexed family and exact upstream theta_CAR
transport are still distinct obligations, followed by irreducibility.
-/

namespace FCP.BFSSFermionF2B2MixedAll
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF2
open FCP.BFSSFermionF2B2Mixed FCP.BFSSFermionF2B2MixedDiag

private abbrev BFSSOp :=
  OAI.BFSSQuantum.Fermion 2 →L[ℂ] OAI.BFSSQuantum.Fermion 2

/-- The two Majorana components anticommute for every pair of modes. -/
theorem majorana01_car_all (i j : Fin 24) :
    majorana0 i * majorana1 j + majorana1 j * majorana0 i =
      (0 : BFSSOp) := by
  by_cases hij : i = j
  · subst j
    exact majorana01_car_self i
  · exact majorana01_car_ne i j hij

#print axioms majorana01_car_all

end
end FCP.BFSSFermionF2B2MixedAll

/-!
Independent BFSS SU(2) formalization contribution by Evan T. Kotler (2026).
Research DOI: https://doi.org/10.5281/zenodo.23291242
FCP source: b60baa806dab3f0b296229a78f70e07b787544ab, experiments/openai-math-su2-concrete-potential/SU2FermionF2B2MixedAllProbe.lean
Copyright (c) 2026 Evan T. Kotler. SPDX-License-Identifier: Apache-2.0.
Build status: integrated candidate; upstream port NOT YET independently verified.
OpenAI retains credit for the original BFSS definitions on which this work builds.
-/
