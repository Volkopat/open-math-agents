import Mathlib

/-!
# A239800: every positive integer is a value of A016014

Source: https://oeis.org/A239800
Credit: @avivorly

A016014 (%N): Least k such that 2*n*k + 1 is a prime.

A239800 (%N): First appearance of n in A016014, or 0 if n never occurs.

Claim (A239800 %C): Conjecture: a(n) > 0 for all n. - _Jianing Song_, Mar 09 2021

Conventions:
- Both entries have offset 1: the index `n` and the multiplier `k` range over `n ≥ 1` and `k ≥ 1`.
- `A016014 n` is the infimum of the set of `k ≥ 1` such that `2*n*k + 1` is prime. For `n ≥ 1` this set is nonempty by
  Dirichlet's result on primes in arithmetic progressions (`2*n` and `1` are coprime), so `A016014 n` is the least such
  `k`, as in the entry. (For `n = 0` the set is empty and the value is `0`; `n = 0` is outside the entry and is excluded
  by `1 ≤ n` below.)
- `a(K) > 0` holds exactly when `K` occurs in A016014, that is, when `A016014 n = K` for some `n ≥ 1` (then `a(K)` is the
  least such `n`). So the claim reads: every `K ≥ 1` is a value of A016014 at some index `n ≥ 1`.
-/

namespace OMA.S_oeis_a239800

/-- A016014: the least `k ≥ 1` such that `2*n*k + 1` is prime (the infimum of that set of `k`). -/
noncomputable def A016014 (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ (2 * n * k + 1).Prime}

theorem main : ∀ K : ℕ, 1 ≤ K → ∃ n : ℕ, 1 ≤ n ∧ A016014 n = K := by
  sorry

end OMA.S_oeis_a239800
