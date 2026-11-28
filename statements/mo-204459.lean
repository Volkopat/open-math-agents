import Mathlib

/-!
# Is the integral `I_{n,p,a} = ∫₀^{∞-} e^{iat} (e^{it} - e^{-it})ⁿ / t^{p+1} dt` always nonzero?

Source: https://mathoverflow.net/questions/204459
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 204459, Iosif Pinelis, May 2015): let
`I_{n,p,a} := ∫_0^{∞-} g_{n,a}(t) / t^{p+1} dt` with `g_{n,a}(t) := e^{iat} (e^{it} - e^{-it})ⁿ`, under
the conditions `(∗)`: `n ∈ ℕ`, `-∞ < a < ∞`, `p_{n,a} < p < n`, where `p_{n,a}` is `0` or `-1`
according as `a` belongs to `{2j - n : j = 0, …, n}` or not. "Do there exist `n`, `p` and `a` such
that conditions `(∗)` hold and `I_{n,p,a} = 0`? It appears that the answer is negative." The asker's
own partial answer proves `I_{n,p,a} ≠ 0` when `|a| > n` (non-integer `p`) and for all large
enough `n`; the general case is open. This file states the expected negative answer.

Modelling choices:
* `∫_0^{∞-}` is an improper integral at infinity: the limit as `T → ∞` of `∫_0^T`. The integrand
  is integrable near `0` because `p < n`. The statement asserts that this limit exists and is
  nonzero (the source treats `I_{n,p,a}` as a well-defined number, given by its closed formula).
* `t^{p+1}` for `t > 0` is the real power `t ^ (p + 1)`, cast to `ℂ`.
* `n ∈ ℕ` is read as `n ≥ 1` (the source's integrand `(e^{it} - e^{-it})ⁿ` comes from an `n`-fold
  symmetric difference; with `n = 0` the integral is a plain Fourier-type integral and is not the
  object of the question).
-/

namespace OMA.S_mo_204459

open MeasureTheory Filter Topology

/-- `g_{n,a}(t) = e^{iat} (e^{it} - e^{-it})ⁿ`. -/
noncomputable def g (n : ℕ) (a t : ℝ) : ℂ :=
  Complex.exp (Complex.I * a * t) *
    (Complex.exp (Complex.I * t) - Complex.exp (-(Complex.I * t))) ^ n

/-- `p_{n,a}`: `0` if `a ∈ {2j - n : j = 0, …, n}`, and `-1` otherwise. -/
noncomputable def pLow (n : ℕ) (a : ℝ) : ℝ :=
  open Classical in if ∃ j ≤ n, a = 2 * (j : ℝ) - n then 0 else -1

/-- **MathOverflow 204459 (expected answer).** Under conditions `(∗)` the improper integral
`I_{n,p,a}` converges to a nonzero value. -/
theorem main :
    ∀ (n : ℕ) (p a : ℝ), 1 ≤ n → pLow n a < p → p < n →
      ∃ L : ℂ, L ≠ 0 ∧
        Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, g n a t / ((t ^ (p + 1) : ℝ) : ℂ)) atTop
          (𝓝 L) := by
  sorry

end OMA.S_mo_204459
