## Contributions

- 2026-10-28 @chelsinchaos (Chelsea A. McElveen): Added NOTES.md and checks/ (executable toy model of Sections 2.3–2.7, structural remarks on Section 2.7, expository suggestions); implementation and drafting assisted by Claude (Anthropic) ([PR #60](https://github.com/mathcommunity/oai-math-revised/pull/60)).
- 2026-10-30 @schmittj (Johannes Schmitt): Reduced these notes to the agreed format after a review found mathematical problems in the structural remarks, and removed checks/ (the script remains in the linked repository); details are in the comment on PR #60. Drafted with Claude Code; reviewed with Fable and Codex ([PR #68](https://github.com/mathcommunity/oai-math-revised/pull/68)).
- 2026-10-29 @Beltran12138 (ZHAO Han): Added a review recording an independent build of the Lean formalization and a comparison of its statement with the solution module. Prepared with Claude Code; checked by the contributor ([PR #62](https://github.com/mathcommunity/oai-math-revised/pull/62)).

## Follow-up works

- [Chelsea A. McElveen, *Measurement-Indexed Counting: An Executable Study of OpenAI's #3-SAT Algorithm, Semiring Component Caches, and the Limits of Oblivious Sampling*](https://github.com/chelsinchaos/measurement-indexed-counting/tree/7a73e39b11c71d2b3c7209074e04e84208612b58) (manuscript with code and dataset, 28 October 2026). Contains an exact Python model of Sections 2.3–2.7 whose values are compared with brute force at $n\le 14$, using heuristic schedules in place of the paper's derandomized ones; its component analysis concerns a simplified hypergraph, not the replacement forms of Section 2.7.

## Constructive comments / reviews

- [McElveen, `measurement_toy.py`](https://github.com/chelsinchaos/measurement-indexed-counting/blob/7a73e39b11c71d2b3c7209074e04e84208612b58/code/measurement_toy.py): In the toy's extension of Section 2.7 to $R=Q+1$, outside the paper's parameter regime, choosing the interpolation interval $\{0,\ldots,Q\}$ gives $M_0=I$ and no measurements, with replacement forms of degree up to $Q$; this illustrates the remark that a different form at each point "would generally cost degree $Q$" (run with `--design aux --Q 3 --R 4`).
- [oai-math-recheck, family 378](https://github.com/Beltran12138/oai-math-recheck/tree/4565162/families/378): Independent re-check at openai/math `7ef5c0c`, which the comparator run of 2026-10-26 predates: all 3,977 modules built, the theorem rests only on the three standard axioms, and the challenge and solution statements elaborate to identical constants, definition bodies included; this is not a comparator run.

## People interested in meeting to work on digestion
