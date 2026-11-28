import Mathlib

/-!
# Does the series $\sum_{n \ge 1} \frac{\tan n}{n^2}$ converge?

Source: https://math.stackexchange.com/questions/470527
Credit: @SulkBash

## The problem (as the source states it)

Does the sum
$$\sum_{n=1}^{\infty} \frac{\tan n}{n^2}$$
converge?

The terms are large when $n$ is close to an odd multiple of $\frac{\pi}{2}$, so the behaviour of
the series is tied to how well $\pi$ can be approximated by rationals (its irrationality measure),
as for the Flint Hills series $\sum \frac{1}{n^3 \sin^2 n}$. The question is open.

## Formalization notes

* Angles are in radians, and `Real.tan x = Real.sin x / Real.cos x`. For every positive integer
  `n` we have `Real.cos n ≠ 0`, because `π` is irrational. So the junk value of `Real.tan` at
  zeros of `cos` never occurs, and every term is the genuine `tan n / n²`.
* "The series converges" is read in the standard sense: its partial sums
  `∑ n ∈ Finset.Icc 1 N, Real.tan n / n ^ 2` tend to a finite real limit as `N → ∞`.
  - This is deliberately not Mathlib's `Summable`. For real series, `Summable` means unconditional
    convergence, which is equivalent to absolute convergence, a strictly stronger property.
  - Absolute convergence implies `main`, so a proof of `Summable` would also prove `main`.
* The source asks a yes/no question and does not predict the answer. `main` states the answer
  yes: the series converges. A disproof of `main` is the answer no: the partial sums have no
  finite limit.
-/

namespace OMA.S_mse_470527

open Filter Topology

/-- The series $\sum_{n \ge 1} \frac{\tan n}{n^2}$ converges: its partial sums have a finite
limit. -/
theorem main :
    ∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, Real.tan n / (n : ℝ) ^ 2) atTop (𝓝 L) := by
  sorry

end OMA.S_mse_470527
