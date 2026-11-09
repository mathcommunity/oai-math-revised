## Contributions

- 2026-11-06 @gilheumpark-bit: Added 14 classical references across Sections 1–6 and 8 and connected all 9 previously uncited entries in `build/references.bib` to `\cite{...}` calls in the text with numbering unchanged. Drafted with AI assistance; sources, calculations, and Lean proofs checked by the contributor ([PR #76](https://github.com/mathcommunity/oai-math-revised/pull/76)).

## Follow-up works

## Constructive comments / reviews

- [ultari-proof-anatomy, case 006](https://github.com/gilheumpark-bit/ultari-proof-anatomy/tree/9a3b5350b496c1e1c5252f1d77a09a8b4670fb1e/anatomy/006-openai-376-navier-stokes): Lean 4, SymPy, and PyTorch checks of the family 376 formalization across `lean/ComparatorChallenges/` and `lean/OAI/`, plus a classical literature and bibliography audit of `build/` (covering the affine curl potential in `BoxTransport/Flow.lean`, the $L^2$ energy comparison in `BalancedTransport/Comparison.lean`, the 2+1D passive-scalar mild solution in `VelocityDetection/MildScalar.lean`, the zero-pressure residual identity $f = f_0 + \nu f_1$ in `BalancedTransport/BoxCoding.lean`, the duplicate statement in `ForcedNavierStokesComputation.lean` and `BalancedThreeStack.lean`, the unused `_hcomputable : ComputableReal ν` premise in `VelocityDetection/MainResult.lean:51`, the 650 `OAI/` modules not imported by the six challenge entrypoints, the `9/22` (`40.9%`) BibTeX entries in `build/references.bib` previously uncited via `\cite`, and the classical original human references for `11/15` (`73.3%`) previously uncited manuscript sections).

## People interested in meeting to work on digestion
