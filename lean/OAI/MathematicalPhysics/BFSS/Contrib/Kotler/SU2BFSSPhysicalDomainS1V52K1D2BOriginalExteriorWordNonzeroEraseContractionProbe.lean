import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.SU2BFSSPhysicalDomainS1V52K1D2AOriginalExteriorCoordinateWordContractionProbe

/-! Owner FCP source-only port, original cc608e2282e1b32bb11bbb64424e4775b28138e2; Git blob 9a0a119273e3215f05105344ac64f0a9c74853ac.
Imports alone have been restructured; theorem statements/proof bodies unchanged.
The omitted original Spin ancestry is not claimed qualified by this port.
Status: provisional pending fresh owner strict-gate acceptance. -/

/-!
K1D2B — coordinate exterior word contraction erases a present
original source label up to a PROVED nonzero real scalar.

No assumption about a guessed flattened 48-label order. For every
Nodup list of literal original Source48Label, a present coordinate
contracts to a nonzero scalar multiple of the word with that label
erased. This is a list-level precursor to the true ordered
Finset Source48Label exterior basis coefficient extraction.

Staged until a genuine strict source-pinned Lean/axiom gate passes.
The full exterior common-kernel scalar lemma remains OPEN.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace FCP.BFSSS1V52K1D2B
noncomputable section
open FCP.BFSSS1V0
open FCP.BFSSS1V52K1D2A

private abbrev E := ExteriorAlgebra ℝ Source48Vector
private abbrev Q0 : QuadraticForm ℝ Source48Vector := 0

/-- In any original 48-label coordinate exterior word with distinct
labels, contraction at a PRESENT label equals the original word
after erasure, times a proved NONZERO real sign-like scalar.
No finite-dimensional brute-force enumeration or graded
scalar-kernel hypothesis is used. -/
theorem originalExteriorCoordinateWord_contract_present_nonzero_erase
    (j : Source48Label) (xs : List Source48Label)
    (hnd : xs.Nodup) (hj : j ∈ xs) :
    ∃ c : ℝ, c ≠ 0 ∧
      CliffordAlgebra.contractLeft (Q := Q0)
        (LinearMap.proj j : Module.Dual ℝ Source48Vector)
        (originalExteriorCoordinateWord xs) =
        c • originalExteriorCoordinateWord (xs.erase j) := by
  classical
  induction xs with
  | nil =>
      simp at hj
  | cons k ks ih =>
      have hndks : ks.Nodup := (List.nodup_cons.mp hnd).2
      by_cases heq : k = j
      · subst k
        have hn : j ∉ ks := (List.nodup_cons.mp hnd).1
        refine ⟨1, one_ne_zero, ?_⟩
        simpa using
          originalExteriorCoordinateWord_leading_contraction j ks hn
      · have hmem : j ∈ ks := by
          rcases List.mem_cons.mp hj with h | h
          · exact False.elim (heq h.symm)
          · exact h
        obtain ⟨c, hc, hw⟩ := ih hndks hmem
        refine ⟨-c, neg_ne_zero.mpr hc, ?_⟩
        rw [originalExteriorCoordinateWord_cons]
        rw [CliffordAlgebra.contractLeft_ι_mul]
        have hzero :
            (LinearMap.proj j : Module.Dual ℝ Source48Vector)
              (Pi.single k (1 : ℝ) : Source48Vector) = 0 := by
          simp [heq]
        rw [hzero, hw]
        simp [originalExteriorCoordinateWord_cons, heq,
          neg_smul]

#print axioms originalExteriorCoordinateWord_contract_present_nonzero_erase

end
end FCP.BFSSS1V52K1D2B
