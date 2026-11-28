import Mathlib

/-!
# A227071: the least exponent with the same set of `k` such that `k^m` ends with `k`

Source: https://oeis.org/A227071
Credit: @avivorly

A227071: Let s(m) = the set of k > 0 such that k^m ends with k. Then a(n) = least m such that s(m) = s(n).
(Offset 1; data 1, 2, 3, 2, 5, 6, 3, 2, 9, 2, 11, 2, 5, 2, 3, 6, 17, ...)

A132741: Largest divisor of n having the form 2^i*5^j.

Conjecture (Eric M. Schmidt, Jul 30 2013, in the entry): a(n+1) = A132741(n) + 1.

Conventions:
- `k^m` ends with `k` is read in decimal: with `d = (Nat.digits 10 k).length` the number of decimal digits of `k`,
  the last `d` digits of `k^m` are those of `k`, that is `k ^ m % 10 ^ d = k`.
- `s m` is the set of all such `k > 0`, as a `Set ℕ`.
- `a n` is `sInf {m | 0 < m ∧ s m = s n}`, the least positive `m` with `s m = s n`. For `n ≥ 1` that set contains
  `n`, so the infimum is its least element (A227071 has offset 1; `a 0` is not used). Requiring `0 < m` changes
  nothing for `n ≥ 1`: `s 0 = {1}`, while `5 ∈ s n` for every `n ≥ 1`.
- `A132741 n` is defined literally, as the largest divisor of `n` of the form `2^i * 5^j` with `i, j ≥ 0`: the
  `sSup` of that set of divisors, which for `n ≥ 1` contains `1` and is bounded by `n` (so it is
  `2^v2(n) * 5^v5(n)`).
- The conjecture is stated for all `n ≥ 1` (A132741 has offset 1).
-/

namespace OMA.S_oeis_a227071

/-- `s m`: the positive integers `k` such that `k ^ m` ends with `k` in decimal. -/
def s (m : ℕ) : Set ℕ := {k | 0 < k ∧ k ^ m % 10 ^ (Nat.digits 10 k).length = k}

/-- A227071: `a n` is the least positive `m` with `s m = s n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | 0 < m ∧ s m = s n}

/-- A132741: the largest divisor of `n` of the form `2^i * 5^j`. -/
noncomputable def A132741 (n : ℕ) : ℕ := sSup {d | d ∣ n ∧ ∃ i j : ℕ, d = 2 ^ i * 5 ^ j}

theorem main : ∀ n ≥ 1, a (n + 1) = A132741 n + 1 := by
  sorry

end OMA.S_oeis_a227071
