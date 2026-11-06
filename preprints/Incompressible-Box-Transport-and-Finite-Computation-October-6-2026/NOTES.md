## Contributions

- 2026-11-06 @gilheumpark-bit: Added 19 missing classical references across Sections 1–6 and 8 (von Helmholtz 1858; Gronwall 1919; Weyl 1940; Prodi 1959; Minsky 1961, 1967; Serrin 1962, 1963; Ladyzhenskaya 1969; Krygin 1971; Banyaga 1978; Constantin–Foias 1988; Pour-El–Richards 1989; Koiran–Cosnard–Garzon 1994; Siegelmann–Sontag 1995; Weihrauch 2000; Axelsen–Glück 2011; Galdi 2011; Morita 2017), connected all 9 previously uncited entries in `references.bib` (Nash 1958; Moser 1965; Aronson 1968; Etnyre–Ghrist 2000; Tao 2016; Cardona–Miranda–Peralta-Salas 2022, 2025; Cardona–Miranda–Peralta-Salas–Presas 2023; Cardona 2025) to `\cite{...}` calls in the text with numbering unchanged, and linked a standalone Lean 4, SymPy, and PyTorch check of the family 376 formalization. Drafted with AI assistance; sources, calculations, and Lean proofs checked by the contributor ([PR #76](https://github.com/mathcommunity/oai-math-revised/pull/76)).

## Follow-up works

## Constructive comments / reviews

- [ultari-proof-anatomy, case 006](https://github.com/gilheumpark-bit/ultari-proof-anatomy/tree/9a3b5355d44a5bb2054519cdb4e345373d40befe/anatomy/006-openai-376-navier-stokes): Lean 4, SymPy, and PyTorch checks of the family 376 formalization across `lean/ComparatorChallenges/` and `lean/OAI/`, plus a classical literature and bibliography audit of `build/` (covering the affine curl potential in `BoxTransport/Flow.lean`, the $L^2$ energy comparison in `BalancedTransport/Comparison.lean`, the 2+1D passive-scalar mild solution in `VelocityDetection/MildScalar.lean`, the zero-pressure residual identity $f = f_0 + \nu f_1$ in `BalancedTransport/BoxCoding.lean`, the duplicate statement in `ForcedNavierStokesComputation.lean` and `BalancedThreeStack.lean`, the unused `_hcomputable : ComputableReal ν` premise in `VelocityDetection/MainResult.lean:51`, the 650 `OAI/` modules not imported by the six challenge entrypoints, the `9/22` (`40.9%`) BibTeX entries in `build/references.bib` previously uncited via `\cite`, and the classical original human references for `11/15` (`79.7%`) previously uncited manuscript sections).

## People interested in meeting to work on digestion
