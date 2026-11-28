import Mathlib

/-!
# Erdős Problem 1117

Source: https://www.erdosproblems.com/1117
Credit: @shc261392

The source: let `f(z)` be an entire function which is not a monomial. Let `ν(r)` count the number
of `z` with `|z| = r` such that `|f(z)| = max_{|z|=r} |f(z)|` (a finite quantity when `f` is not a
monomial). Is it possible for `limsup ν(r) = ∞`? Is it possible for `liminf ν(r) = ∞`?

The source records that the first question was answered yes by Herzog and Piranian [HePi68]; the
second is still open. This file states the open second question, in its affirmative form: a proof
of `main` answers it yes, a proof of `¬ main` answers it no.

Reading used here:
* "entire" is `Differentiable ℂ f`; "monomial" is a function `z ↦ c * z ^ n` (`c : ℂ`, `n : ℕ`),
  which includes the constant functions.
* `ν(r)` is the number of points of the circle `|z| = r` where `‖f z‖` equals its supremum over
  that circle (the supremum is a maximum, the circle being compact).
* The limits are taken as `r → ∞` through the reals; for a function with values in `ℕ`,
  `liminf ν(r) = ∞` means `ν(r) → ∞`.
-/

namespace OMA.S_erdos_1117

open Filter

/-- `ν f r`: the number of `z` with `‖z‖ = r` at which `‖f z‖` is maximal on that circle. -/
noncomputable def nu (f : ℂ → ℂ) (r : ℝ) : ℕ :=
  Set.ncard {z : ℂ | ‖z‖ = r ∧ ‖f z‖ = sSup ((fun w => ‖f w‖) '' Metric.sphere (0 : ℂ) r)}

theorem main :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (¬ ∃ (c : ℂ) (n : ℕ), f = fun z => c * z ^ n) ∧
      Tendsto (nu f) atTop atTop := by
  sorry

end OMA.S_erdos_1117
