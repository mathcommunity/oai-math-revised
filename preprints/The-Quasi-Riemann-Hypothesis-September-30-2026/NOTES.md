## Contributions

- 2026-10-31 @gilheumpark-bit: Added NOTES.md linking a standalone Lean 4 and SymPy analysis of the rational and polynomial parameter bounds in the DirichletL formalization. Drafted with AI assistance; calculations and Lean proofs checked by the contributor.

## Follow-up works

## Constructive comments / reviews

- [ultari-proof-anatomy, case 001](https://github.com/gilheumpark-bit/ultari-proof-anatomy/tree/9904079434d921fa0cb3b6136b1cc24a6f33b56c/anatomy/001-openai-003-qrh) (independent parameter and exponent analysis, 2026-10-31): Standalone Lean 4 (`v4.29.0-rc8`, zero `sorry`, no Mathlib dependency) and SymPy reconstruction of 40 rational and integer parameter theorems from `lean/OAI/NumberTheory/DirichletL/` (`qrh_exponent_and_parameter_bounds.lean` and `qrh_continuation_and_rescaling.lean`, with English and Korean guides).
  - Derives the closed-form quadratic stationary point $a^* = 323/276 - 35\sqrt{16354}/9384 \approx 0.693319$ of `balancedExponent` at $y = 0$ in `Endpoint.lean` (approximated there by the rational SOS point $\delta = 79/204$, $a = 283/408 \approx 0.693627$ with margin $7/30672$) and the linear floor-margin root $a_{\max} = 37/72 \approx 0.513889$ ($\eta = 1/72$) in `CentralExponent.lean`.
  - Compares the individual square-root $Z$-exponents from `GramScaleLoss.lean`, `GramBound.lean`, and `LowSourceScales.lean` (`17/96`, $(14 + 17\delta)/96$, `18/96` at $L \asymp Z^{1/6}$) against the bundled upper bound $(18 + 23\delta)/96$ in `LowGramScale.lean` (a minimum gap of $215/3264$ at $\delta = 79/204$, or $592.35\times$ the baseline SOS margin $49/440640$), and notes that `compensated_geometry` in `Parameters.lean` is unreferenced in the codebase while `eventually_compensated_source_scales` in `LowSourceScales.lean` uses $L \le Z^{11/48}$ with $1/16$ exponent slack above $1/6$.
  - Formalizes over `Int` and `Rat` the vanishing of 6 of the 8 non-principal Gauss-sum branches for $m \ge 2$ in `HighRowsTail.lean` (relaxing $z_{\mathrm{re}} \ge 1/6$ to $1/12$), the polynomial cancellation of the $(1 - V)$ denominator in `Local.lean` (lowering the prime-norm threshold from $Q \ge 480$ to $Q \ge 112$), and the second-order Euler factor $(1 - R)$ cancelling all five first-order simple-pole terms.
  - Not shown: this repository checks the rational, integer, and polynomial identities underlying the parameter tables and exponent comparisons; it does not re-formalize the complex-analytic Mellin contour integrals or operator norms.

## People interested in meeting to work on digestion
