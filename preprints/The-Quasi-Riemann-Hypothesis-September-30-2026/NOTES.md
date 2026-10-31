## Contributions

- 2026-10-31 @gilheumpark-bit: Added NOTES.md linking a standalone Lean 4 and SymPy reconstruction of the rational and polynomial parameter bounds in the DirichletL formalization. Drafted with AI assistance; calculations and Lean proofs checked by the contributor ([PR #70](https://github.com/mathcommunity/oai-math-revised/pull/70)).

## Follow-up works

## Constructive comments / reviews

- [ultari-proof-anatomy, case 001](https://github.com/gilheumpark-bit/ultari-proof-anatomy/tree/9904079434d921fa0cb3b6136b1cc24a6f33b56c/anatomy/001-openai-003-qrh): Standalone Lean 4 (`v4.29.0-rc8`, 40 theorems, no Mathlib dependency) and SymPy reconstruction of the rational and integer parameter bounds in `lean/OAI/NumberTheory/DirichletL/`, recording the exact quadratic stationary point $a^* = 323/276 - 35\sqrt{16354}/9384$ behind $\delta = 79/204$ in `Endpoint.lean`, the floor-margin root $a_{\max} = 37/72$ in `CentralExponent.lean`, the $215/3264$ ($592.35\times$) gap between the componentwise Gram exponents in `GramBound.lean` and the bundled bound in `LowGramScale.lean`, the vanishing of 6 of 8 non-principal Gauss branches for $m \ge 2$ in `HighRowsTail.lean`, and the $(1 - V)$ polynomial cancellation ($Q \ge 480 \to 112$) in `Local.lean`; this checks the parameter arithmetic and polynomial identities only, not the complex-analytic contour integrals.

## People interested in meeting to work on digestion
