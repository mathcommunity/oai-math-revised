## Contributions

- 2026-11-06 @gilheumpark-bit: Added 14 classical references across Sections 1–6 and 8 and connected all 9 previously uncited entries in `build/references.bib` to `\cite{...}` calls in the text with numbering unchanged. Drafted with AI assistance; sources, calculations, and Lean proofs checked by the contributor ([PR #76](https://github.com/mathcommunity/oai-math-revised/pull/76)).

## Follow-up works

## Constructive comments / reviews

- [ultari-proof-anatomy, case 006](https://github.com/gilheumpark-bit/ultari-proof-anatomy/tree/9a10b0ba9e1549f8c2af98d16b0926204e3295af/anatomy/006-openai-376-navier-stokes): Standalone Lean 4 (`45` theorems) and SymPy checks across `lean/ComparatorChallenges/` and `lean/OAI/`, plus a classical literature and bibliography review of `build/` (covering the affine curl potential in `BoxTransport/Flow.lean`, the $L^2$ energy comparison in `BalancedTransport/Comparison.lean`, the 2+1D passive-scalar mild solution in `VelocityDetection/MildScalar.lean`, the disclosed zero-pressure residual identity $f = f_0 + \nu f_1$ in `BalancedTransport/BoxCoding.lean` and `docs/376.md` alongside the `650` of `1,004` `OAI/` modules [including periodic solenoidal `Solenoidal.lean` and `ForcedComputation/`] not imported by the six challenge entrypoints, `50/51` shared declarations between `ForcedNavierStokesComputation.lean` and `BalancedThreeStack.lean`, helper-`def` `(by sorry)` in `NavierStokesVelocity.lean:454` [`Prop` proof-irrelevant `isDefEq` with `TapeCodes.lean:32-33`], the unused `_hcomputable : ComputableReal ν` premise in `VelocityDetection/MainResult.lean:51`, the `9/22` (`40.9%`) previously uncited `build/references.bib` entries, and `14` primary classical references across `build/`).

## People interested in meeting to work on digestion
