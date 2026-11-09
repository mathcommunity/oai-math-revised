import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2FermionF3B4SelectorProbe

/-!
# BFSS fermions F3-B5 — full-vector occupation-coordinate extraction

The existing pinned exterior Fock basis really spans all 24-mode finite
Fock vectors. Transport that basis decomposition through the accepted
coordinate and BFSS unitary equivalences, then use Gate #65's exact
basis-selector theorem on arbitrary BFSS vectors.

No irreducibility assumption, unproved completeness assumption, or
replacement CAR representation is introduced.
-/

namespace FCP.BFSSFermionF3B5
noncomputable section

open FCP.BFSSFermionF1 FCP.BFSSFermionF3B2 FCP.BFSSFermionF3B4
open OAI.Laughlin.Fock OAI.ContinuumCoulomb.HubbardGlobal
open scoped BigOperators

private abbrev BFSSFermion := OAI.BFSSQuantum.Fermion 2

/-- The exact pinned exterior Fock basis coordinate of a BFSS vector,
transported through the inverse of the already-accepted F1 equivalences. -/
noncomputable def occupationCoeff (x : BFSSFermion)
    (A : Finset (Fin 24)) : ℂ :=
  (fockBasis 23).repr
    ((fockCoordinates 23).symm (fockBFSSUnitary.symm x)) A

/-!
The next steps are proof-term decomposition rather than raised kernel budgets.
Each named fact is checked separately, and the huge occupation index is
never enumerated by `rfl` or unrestricted `simp`.
-/

private theorem occupationCoeff_eq (x : BFSSFermion) (A : Finset (Fin 24)) :
    occupationCoeff x A =
      (fockBasis 23).repr
        ((fockCoordinates 23).symm (fockBFSSUnitary.symm x)) A := rfl

private theorem occupationKet_eq (A : Finset (Fin 24)) :
    occupationKet A =
      fockBFSSUnitary (fockCoordinates 23 (fockBasis 23 A)) := rfl

private theorem bfssUnitary_apply_symm (x : BFSSFermion) :
    fockBFSSUnitary (fockBFSSUnitary.symm x) = x :=
  fockBFSSUnitary.apply_symm_apply x

private theorem fockCoordinates_apply_symm (v : FockCoordinateSpace 23) :
    fockCoordinates 23 ((fockCoordinates 23).symm v) = v :=
  (fockCoordinates 23).apply_symm_apply v

private theorem recover_from_preimage (x : BFSSFermion) :
    x = fockBFSSUnitary
      (fockCoordinates 23
        ((fockCoordinates 23).symm (fockBFSSUnitary.symm x))) := by
  calc
    x = fockBFSSUnitary (fockBFSSUnitary.symm x) :=
      (bfssUnitary_apply_symm x).symm
    _ = fockBFSSUnitary
          (fockCoordinates 23
            ((fockCoordinates 23).symm (fockBFSSUnitary.symm x))) :=
      congrArg fockBFSSUnitary
        (fockCoordinates_apply_symm (fockBFSSUnitary.symm x)).symm

/-!
Gate #69 proved the need for an earlier transparency boundary:
`LinearEquiv.map_sum` is not a field in the pinned API, and the
specialized `push_basis_expansion` still overburdened the kernel.
First establish the basis-transport identity *polymorphically* before
specializing to the 24-mode Fock index and BFSS Hilbert space.
-/

private theorem generic_basis_map_sum_repr
    {ι V W : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (b : Module.Basis ι ℂ V) (f : V →ₗ[ℂ] W) (v : V) :
    f v = ∑ i : ι, b.repr v i • f (b i) := by
  calc
    f v = f (∑ i : ι, b.repr v i • b i) :=
      congrArg f (b.sum_repr v).symm
    _ = ∑ i : ι, b.repr v i • f (b i) := by
      simp only [map_sum, map_smul]

/-- The accepted F1 coordinate and Hilbert equivalences, composed
as an ordinary linear equivalence without changing their definitions. -/
private noncomputable def fockToBFSS : Space 23 ≃ₗ[ℂ] BFSSFermion :=
  (fockCoordinates 23).trans fockBFSSUnitary.toLinearEquiv

private theorem fockToBFSS_apply (y : Space 23) :
    fockToBFSS y = fockBFSSUnitary (fockCoordinates 23 y) := rfl

private theorem fockToBFSS_basis (B : Finset (Fin 24)) :
    fockToBFSS (fockBasis 23 B) = occupationKet B := rfl

/-- Specialize the already-checked GENERIC linear-map basis expansion;
do not separately kernel-check a 2^24-indexed mapped-sum rewrite. -/
private theorem push_basis_expansion (y : Space 23) :
    fockBFSSUnitary (fockCoordinates 23 y) =
      ∑ B : Finset (Fin 24),
        (fockBasis 23).repr y B • occupationKet B := by
  have hg :
      fockToBFSS y =
        ∑ B : Finset (Fin 24),
          (fockBasis 23).repr y B • fockToBFSS (fockBasis 23 B) :=
    generic_basis_map_sum_repr (fockBasis 23) fockToBFSS.toLinearMap y
  calc
    fockBFSSUnitary (fockCoordinates 23 y) = fockToBFSS y :=
      (fockToBFSS_apply y).symm
    _ = ∑ B : Finset (Fin 24),
          (fockBasis 23).repr y B • fockToBFSS (fockBasis 23 B) := hg
    _ = ∑ B : Finset (Fin 24),
          (fockBasis 23).repr y B • occupationKet B := by
      refine Finset.sum_congr rfl ?_
      intro B _
      exact congrArg (fun z : BFSSFermion => (fockBasis 23).repr y B • z)
        (fockToBFSS_basis B)

/-- Every exact BFSS Fermion 2 vector has its full genuine transported
24-mode occupation-basis expansion. -/
theorem occupationExpansion (x : BFSSFermion) :
    x = ∑ B : Finset (Fin 24), occupationCoeff x B • occupationKet B := by
  calc
    x = fockBFSSUnitary
          (fockCoordinates 23
            ((fockCoordinates 23).symm (fockBFSSUnitary.symm x))) :=
      recover_from_preimage x
    _ = ∑ B : Finset (Fin 24),
          (fockBasis 23).repr
            ((fockCoordinates 23).symm (fockBFSSUnitary.symm x)) B •
              occupationKet B :=
      push_basis_expansion _
    _ = ∑ B : Finset (Fin 24),
          occupationCoeff x B • occupationKet B := by
      refine Finset.sum_congr rfl ?_
      intro B _
      exact congrArg (fun c : ℂ => c • occupationKet B)
        (occupationCoeff_eq x B).symm

private theorem selector_on_summand
    (A B : Finset (Fin 24)) (x : BFSSFermion) :
    occupationCoeff x B • occupationSelector A (occupationKet B) =
      if A = B then occupationCoeff x B • occupationKet B else 0 := by
  rw [occupationSelector_occupationKet]
  by_cases h : A = B
  · simp only [_root_.ite_eq_left h]
  · simp only [_root_.ite_eq_right h, smul_zero]

/-- The concrete ordered occupation selector extracts the actual coefficient
of one occupation ket from any BFSS fermion vector. -/
theorem occupationSelector_apply (A : Finset (Fin 24)) (x : BFSSFermion) :
    occupationSelector A x = occupationCoeff x A • occupationKet A := by
  calc
    occupationSelector A x =
        occupationSelector A
          (∑ B : Finset (Fin 24),
            occupationCoeff x B • occupationKet B) :=
      congrArg (occupationSelector A) (occupationExpansion x)
    _ = ∑ B : Finset (Fin 24),
          occupationCoeff x B • occupationSelector A (occupationKet B) := by
      simp only [map_sum, map_smul]
    _ = ∑ B : Finset (Fin 24),
          if A = B then occupationCoeff x B • occupationKet B else 0 := by
      refine Finset.sum_congr rfl ?_
      intro B _
      exact selector_on_summand A B x
    _ = occupationCoeff x A • occupationKet A := by
      have hsingle :
          (∑ B : Finset (Fin 24),
            if A = B then occupationCoeff x B • occupationKet B else 0) =
              (if A = A then occupationCoeff x A • occupationKet A else 0) := by
        apply Finset.sum_eq_single_of_mem A (Finset.mem_univ A)
        intro B _ hBA
        exact _root_.ite_eq_right (Ne.symm hBA)
      simpa only [ite_true] using hsingle

#print axioms occupationExpansion
#print axioms occupationSelector_apply

end
end FCP.BFSSFermionF3B5
