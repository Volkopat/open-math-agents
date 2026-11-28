import Mathlib

/-!
# A Divisor-Sum Analogue of the Collatz Map

Source: https://arxiv.org/abs/2506.01830
(R. Dwivedi and R. Yadav, A Divisor-Sum Analogue of the Collatz Map, Conjecture 1.1)
Credit: @SulkBash

## The problem, as the source states it

Let `σ(n) = ∑_{d ∣ n} d`. For a positive integer `n`, define

  `ℜ(n) := σ(n)` if `n` is odd, and `ℜ(n) := n / 2` if `n` is even,

and set `ℜ⁰(n) := n` and `ℜ^{k+1}(n) := ℜ(ℜ^k(n))` for `k ≥ 0`.

Conjecture 1.1. For every positive integer `n` there exists `k ∈ ℕ` such that `ℜ^k(n) = 1`.

For example `7 ↦ 8 ↦ 4 ↦ 2 ↦ 1` and `9 ↦ 13 ↦ 14 ↦ 7 ↦ 8 ↦ 4 ↦ 2 ↦ 1`. The authors verified
the conjecture for every `n ≤ 10¹⁰`. It implies that there is no odd `2^k`-perfect number
(an odd `N` with `σ(N) = 2^k N`, `k ≥ 1`), since such an `N` lies on a cycle of `ℜ` of length
`k + 1`; in particular it implies that there is no odd perfect number. The number of steps
needed to reach `1` is OEIS A259846.

## Formalization notes

* `σ` is Mathlib's `ArithmeticFunction.sigma 1`, the sum of the divisors.
* `ℜ` is `R` below, defined on all of `ℕ`. The source defines it for positive integers only;
  `R` maps positive integers to positive integers (`σ(n) ≥ 1` for `n ≥ 1`, and `n / 2 ≥ 1` for
  even `n ≥ 2`), so on the positive integers its iterates are exactly the source's. The value
  `R 0 = 0` is never used, because `main` only concerns `n > 0`.
* `ℜ^k` is the `k`-fold iterate `R^[k]`, with `R^[0] n = n`, as in the source.
* `main` is Conjecture 1.1. A disproof is a positive integer whose orbit never reaches `1`
  (an orbit that enters a cycle avoiding `1`, or one that is unbounded).
-/

namespace OMA.S_arxiv_2506_01830

/-- The divisor-sum Collatz map: `σ(n)` for odd `n`, and `n / 2` for even `n`. -/
def R (n : ℕ) : ℕ :=
  if n % 2 = 1 then ArithmeticFunction.sigma 1 n else n / 2

/-- Conjecture 1.1: the orbit of every positive integer under `R` reaches `1`. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ k : ℕ, R^[k] n = 1 := by
  sorry

end OMA.S_arxiv_2506_01830
