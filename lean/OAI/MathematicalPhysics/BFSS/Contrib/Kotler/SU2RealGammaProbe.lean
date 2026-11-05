import Mathlib
import OAI.MathematicalPhysics.BFSS.Core

/-!
# Explicit real Cl(9) gamma matrices, bounded BFSS construction gate

This is a *color-independent* construction of exactly the gamma fields required
by the pinned OpenAI BFSS `AlgebraData 2` API. It does not construct the
48-generator fermionic CAR representation or the full BFSS model.

The signed permutations below encode the exact four-factor real Pauli words

  JIIJ, JIJX, JXJZ, JZJZ, JJIZ, JJXX, JJZX, XIII, ZIII,

where J = [[0,1],[-1,0]], X = [[0,1],[1,0]],
Z = [[1,0],[0,-1]], and I is the 2x2 identity. Every gamma
is a signed permutation matrix on Fin 16.

The finite certificates are proved over integers using kernel-reduced
`decide`, and then transported to real matrices by Int.castRingHom.
No `native_decide`, `sorry`, or extra axioms are used.
-/

namespace FCP.BFSSGamma9

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Each row's column of the unique nonzero entry. -/
private def perm : Fin 9 → Fin 16 → Fin 16
  | 0 => ![
    9, 8, 11, 10, 13, 12, 15, 
    14, 1, 0, 3, 2, 5, 4, 
    7, 6
  ]
  | 1 => ![
    11, 10, 9, 8, 15, 14, 13, 
    12, 3, 2, 1, 0, 7, 6, 
    5, 4
  ]
  | 2 => ![
    14, 15, 12, 13, 10, 11, 8, 
    9, 6, 7, 4, 5, 2, 3, 
    0, 1
  ]
  | 3 => ![
    10, 11, 8, 9, 14, 15, 12, 
    13, 2, 3, 0, 1, 6, 7, 
    4, 5
  ]
  | 4 => ![
    12, 13, 14, 15, 8, 9, 10, 
    11, 4, 5, 6, 7, 0, 1, 
    2, 3
  ]
  | 5 => ![
    15, 14, 13, 12, 11, 10, 9, 
    8, 7, 6, 5, 4, 3, 2, 
    1, 0
  ]
  | 6 => ![
    13, 12, 15, 14, 9, 8, 11, 
    10, 5, 4, 7, 6, 1, 0, 
    3, 2
  ]
  | 7 => ![
    8, 9, 10, 11, 12, 13, 14, 
    15, 0, 1, 2, 3, 4, 5, 
    6, 7
  ]
  | 8 => ![
    0, 1, 2, 3, 4, 5, 6, 
    7, 8, 9, 10, 11, 12, 13, 
    14, 15
  ]

/-- The exact ±1 coefficient in that entry. -/
private def sign : Fin 9 → Fin 16 → ℤ
  | 0 => ![
    1, -1, 1, -1, 1, -1, 1, 
    -1, -1, 1, -1, 1, -1, 1, 
    -1, 1
  ]
  | 1 => ![
    1, 1, -1, -1, 1, 1, -1, 
    -1, -1, -1, 1, 1, -1, -1, 
    1, 1
  ]
  | 2 => ![
    1, -1, -1, 1, 1, -1, -1, 
    1, -1, 1, 1, -1, -1, 1, 
    1, -1
  ]
  | 3 => ![
    1, -1, -1, 1, -1, 1, 1, 
    -1, -1, 1, 1, -1, 1, -1, 
    -1, 1
  ]
  | 4 => ![
    1, -1, 1, -1, -1, 1, -1, 
    1, -1, 1, -1, 1, 1, -1, 
    1, -1
  ]
  | 5 => ![
    1, 1, 1, 1, -1, -1, -1, 
    -1, -1, -1, -1, -1, 1, 1, 
    1, 1
  ]
  | 6 => ![
    1, 1, -1, -1, -1, -1, 1, 
    1, -1, -1, 1, 1, 1, 1, 
    -1, -1
  ]
  | 7 => ![
    1, 1, 1, 1, 1, 1, 1, 
    1, 1, 1, 1, 1, 1, 1, 
    1, 1
  ]
  | 8 => ![
    1, 1, 1, 1, 1, 1, 1, 
    1, -1, -1, -1, -1, -1, -1, 
    -1, -1
  ]

/-- The nine integer signed-permutation gamma matrices. -/
private def gammaInt (a : Fin 9) : Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j => if perm a i = j then sign a i else 0

/-- Integer symmetry certificate, checked at all 9*16*16 entries. -/
private theorem gammaInt_symm_entries :
    ∀ a : Fin 9, ∀ i j : Fin 16, gammaInt a i j = gammaInt a j i := by
  -- Expose the sparse integer entries before requesting a decidable certificate.
  change ∀ a : Fin 9, ∀ i j : Fin 16,
    (if perm a i = j then sign a i else 0) =
    (if perm a j = i then sign a j else 0)
  decide

/-- Sparse matrix multiplication: exactly one nonzero term per row. -/
private theorem gammaInt_mul_apply (a b : Fin 9) (i j : Fin 16) :
    (gammaInt a * gammaInt b) i j =
      if perm b (perm a i) = j then
        sign a i * sign b (perm a i)
      else 0 := by
  classical
  change (∑ k : Fin 16,
      (if perm a i = k then sign a i else 0) *
      (if perm b k = j then sign b k else 0)) = _
  rw [Finset.sum_eq_single (perm a i)]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

/-- All 9*9*16*16 signed-permutation Clifford identities, over integers. -/
private theorem signedPerm_clifford :
    ∀ a b : Fin 9, ∀ i j : Fin 16,
      (if perm b (perm a i) = j then
        sign a i * sign b (perm a i) else 0) +
      (if perm a (perm b i) = j then
        sign b i * sign a (perm b i) else 0) =
        (if a = b then (2 : ℤ) else 0) *
          (if i = j then (1 : ℤ) else 0) := by
  decide

private theorem gammaInt_clifford (a b : Fin 9) :
    gammaInt a * gammaInt b + gammaInt b * gammaInt a =
      if a = b then (1 + 1 : Matrix (Fin 16) (Fin 16) ℤ) else 0 := by
  ext i j
  have h := signedPerm_clifford a b i j
  rw [Matrix.add_apply, gammaInt_mul_apply, gammaInt_mul_apply]
  by_cases hab : a = b <;> by_cases hij : i = j <;>
    simpa [hab, hij, Matrix.add_apply, Matrix.one_apply] using h

/-- Explicit 16x16 real matrices, matching the upstream GammaMatrix type. -/
def gamma (a : OAI.BFSSQuantum.SpaceIndex) : OAI.BFSSQuantum.GammaMatrix :=
  (gammaInt a).map (Int.castRingHom ℝ)

/-- Exact real symmetry condition required by BFSS AlgebraData. -/
theorem gamma_symmetric (a : OAI.BFSSQuantum.SpaceIndex) :
    (gamma a).IsSymm := by
  change (gamma a).transpose = gamma a
  ext i j
  change ((gammaInt a j i : ℤ) : ℝ) = (gammaInt a i j : ℝ)
  exact congrArg (fun x : ℤ => (x : ℝ)) (gammaInt_symm_entries a j i)

/-- Exact real Euclidean Clifford anticommutation required by BFSS. -/
theorem gamma_clifford (a b : OAI.BFSSQuantum.SpaceIndex) :
    gamma a * gamma b + gamma b * gamma a =
      (if a = b then 2 else 0) • (1 : OAI.BFSSQuantum.GammaMatrix) := by
  have h := congrArg
    (fun M : Matrix (Fin 16) (Fin 16) ℤ => M.map (Int.castRingHom ℝ))
    (gammaInt_clifford a b)
  -- Supply the additivity argument explicitly: the generic
  -- Matrix.map_add rewrite left the ring hom's map_add obligation open.
  have hmap_add (X Y : Matrix (Fin 16) (Fin 16) ℤ) :
      (X + Y).map (Int.castRingHom ℝ) =
        X.map (Int.castRingHom ℝ) + Y.map (Int.castRingHom ℝ) := by
    ext i j
    simp [Matrix.add_apply]
  -- Explicitly transport the integer identity matrix to the real one.
  have hmap_one :
      (1 : Matrix (Fin 16) (Fin 16) ℤ).map (Int.castRingHom ℝ) =
        (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
    ext i j
    simp [Matrix.one_apply]
  rw [hmap_add, Matrix.map_mul, Matrix.map_mul] at h
  by_cases hab : a = b
  · subst b
    -- After substituting b, Lean leaves an `if True` under the map.
    -- Reduce the actual `ite_true` form before rewriting mapped addition.
    simp only [ite_true] at h
    rw [hmap_add, hmap_one] at h
    simpa [gamma, two_smul] using h
  · simpa [gamma, hab] using h

/-- A constructed witness to both gamma fields, without theta or a full AlgebraData instance. -/
theorem exists_gamma9 :
    ∃ G : OAI.BFSSQuantum.SpaceIndex → OAI.BFSSQuantum.GammaMatrix,
      (∀ i, (G i).IsSymm) ∧
      (∀ i j, G i * G j + G j * G i =
        (if i = j then 2 else 0) • (1 : OAI.BFSSQuantum.GammaMatrix)) := by
  exact ⟨gamma, gamma_symmetric, gamma_clifford⟩

#print axioms gammaInt_symm_entries
#print axioms signedPerm_clifford
#print axioms gammaInt_mul_apply
#print axioms gamma_symmetric
#print axioms gamma_clifford
#print axioms exists_gamma9

end FCP.BFSSGamma9

/-!
Independent BFSS SU(2) formalization contribution by Evan T. Kotler (2026).
Research DOI: https://doi.org/10.5281/zenodo.23291242
FCP source: b60baa806dab3f0b296229a78f70e07b787544ab, experiments/openai-math-su2-concrete-potential/SU2RealGammaProbe.lean
Copyright (c) 2026 Evan T. Kotler. SPDX-License-Identifier: Apache-2.0.
Build status: integrated candidate; upstream port NOT YET independently verified.
OpenAI retains credit for the original BFSS definitions on which this work builds.
-/
