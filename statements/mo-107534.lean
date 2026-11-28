import Mathlib

/-!
# Is $Q_n(x) = \sigma_{n+1}(x)/\sigma_n(x)$ logarithmically convex on $\mathbb{R}$?

Source: https://mathoverflow.net/questions/107534
Credit: @SulkBash

## The problem (as the source states it)

Write $\sigma_n(x) := 1^x + 2^x + \cdots + n^x$.

Question: is, for every (fixed) integer $n \ge 2$, the function
$$x \in \mathbb{R} \mapsto Q_n(x) := \frac{1^x + 2^x + \cdots + n^x + (n+1)^x}{1^x + 2^x + \cdots + n^x}$$
logarithmically convex on all of $\mathbb{R}$?

Background from the source:
- The question comes from J. van de Lune's work on Riemann sums for $\int_0^1 t^x \, dt$.
- Log-convexity of $Q_n$ would give a simple proof that $h_n(x) = Q_n(x) (n/(n+1))^x$ is
  strictly decreasing.
- It would also prove a conjecture of H. Alzer and A. A. Jagers.
- A comment on the source sketches a proof of log-convexity for $x \ge X_0$, with $X_0$ large.
  The question is open.

## Formalization notes

* `powerSum n x = ∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ x` is $\sigma_n(x)$, with the real power
  `Real.rpow`. Every base `k ≥ 1` is positive, so `(k : ℝ) ^ x = exp (x log k)` for every real `x`.
* $Q_n(x) = \sigma_{n+1}(x) / \sigma_n(x)$ is positive for `n ≥ 1`. So "logarithmically convex
  on all of $\mathbb{R}$" means that `x ↦ log (Q_n x)` is convex on `Set.univ`, which is what
  `main` states.
* The range is `n ≥ 2`, as in the source. The case `n = 1`, where $Q_1(x) = 1 + 2^x$, is
  elementary.
* The source asks a yes/no question and does not predict the answer. `main` states the answer
  yes; a disproof would answer no.
-/

namespace OMA.S_mo_107534

/-- $\sigma_n(x) = 1^x + 2^x + \cdots + n^x$. -/
noncomputable def powerSum (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc 1 n, (k : ℝ) ^ x

/-- For every integer $n \ge 2$, $Q_n(x) = \sigma_{n+1}(x) / \sigma_n(x)$ is logarithmically
convex on $\mathbb{R}$. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ConvexOn ℝ Set.univ (fun x : ℝ => Real.log (powerSum (n + 1) x / powerSum n x)) := by
  sorry

end OMA.S_mo_107534
