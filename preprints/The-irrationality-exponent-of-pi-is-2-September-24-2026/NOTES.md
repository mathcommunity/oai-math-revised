## Contributions

- 2026-11-06 @gilheumpark-bit: Added 13 classical and antecedent references across Sections 2–5 (Abel 1826; Chebyshev 1852; Hardy–Littlewood 1923; Kodaira 1953; Ax 1971; Hanson 1972; Hartshorne 1977; Lang 1982; Faltings 1991; Waldschmidt 2000; Evertse–Ferretti 2002; Gouillon 2006; Fischler–Nakamaye 2014) with numbering unchanged, clarified in `lean/docs/017.md` that Corollary 1.2 is proved in `OAI/NumberTheory/PiExponent/Main.lean` (`flint_hills_summable`), and linked a standalone Lean 4 and symbolic/numerical check of the 869-file `OAI/NumberTheory/PiExponent/` formalization. Drafted with AI assistance; sources, calculations, and Lean proofs checked by the contributor.

## Follow-up works

## Constructive comments / reviews

- [ultari-proof-anatomy, case 010](https://github.com/gilheumpark-bit/ultari-proof-anatomy/tree/b08c8f7a775aa5fbcd7781e65442e2c8ad146802/anatomy/010-openai-017-pi-irrationality-exponent): Standalone Lean 4 (`30` theorems across `3` files, `0 sorry`, `182/182` hypothesis-mutation checks) and Python symbolic/numerical verification (`verify_symbolic_pi017.py`) of the `869`-file (`94,948`-line) `lean/OAI/NumberTheory/PiExponent/` formalization and `build/` manuscript (covering the `100%` import reachability from `Main.lean` with `0` dead modules and `14` unused `_h*` hypothesis parameters; the formal proof of `Corollary 1.2` in `OAI/NumberTheory/PiExponent/Main.lean:29-32` (`flint_hills_summable`) via `Approximation/InterpolationConsequence.lean:21-26` and `Analysis/FlintConsequence.lean:17-28`; the three structural Lean adaptations in `Geometry/RectangularVolume.lean:9-79` ($k^k$ inscribed discrete rectangle vs $2k!$ and enlarged separation constant $C_*^{\text{Lean}}$), `Polynomials/SimplexCounting.lean:40-65` (Euclidean quotient-remainder simplex volume sandwich), and `Analysis/FlintSine.lean:88-90` (`Fin 4` residue grouping constant `16` vs $8/\pi$); and the classical literature lineage across Sections 2–5).

## People interested in meeting to work on digestion
