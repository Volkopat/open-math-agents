import Mathlib

/-!
# The unfair 0-1-polynomials conjecture

Source: https://arxiv.org/abs/2209.09843
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

L. Ghidelli, "Progress on the unfair 0-1-polynomials conjecture using linear recurrences and
numerical analysis" (arXiv:2209.09843), Conjecture 1.2 (algebraic version): let `P, Q ∈ ℝ[t]` be
monic with nonnegative real coefficients, and suppose `R(t) = P(t) Q(t)` has all coefficients in
`{0, 1}`. Then all coefficients of `P` and `Q` lie in `{0, 1}`. (Equivalently, in the paper's
Conjecture 1.1: if independent `ℕ`-valued `X, Y` with finite support have a sum that is uniform on
its support, then `X` and `Y` are uniform on their supports. The general question is attributed to
G. Letac, around 1969; Krasner and Ranulac (1937) settled palindromic `R`. The paper proves the case
`P = x⁵ + a x² + 1`.) This file states Conjecture 1.2.

Modelling choices:
* Polynomials are `Polynomial ℝ`; "coefficients in `{0, 1}`" is `∀ i, coeff i = 0 ∨ coeff i = 1`
  (all but finitely many coefficients are `0` anyway).
-/

namespace OMA.S_arxiv_2209_09843

open Polynomial

/-- All coefficients of `f` are `0` or `1`. -/
def ZeroOne (f : ℝ[X]) : Prop := ∀ i, f.coeff i = 0 ∨ f.coeff i = 1

/-- **Unfair 0-1-polynomials conjecture (Ghidelli, Conjecture 1.2).** -/
theorem main :
    ∀ P Q : ℝ[X], P.Monic → Q.Monic → (∀ i, 0 ≤ P.coeff i) → (∀ i, 0 ≤ Q.coeff i) →
      ZeroOne (P * Q) → ZeroOne P ∧ ZeroOne Q := by
  sorry

end OMA.S_arxiv_2209_09843
