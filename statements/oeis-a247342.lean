import Mathlib

/-!
# A247342: Let b_k=3...3 consist of k>=1 3's. Then a(n) is the smallest k such that the odd part (A000265) of concatenation b_k 2^n  is prime, or a(n)=0 if there is no such prime.

Source: https://oeis.org/A247342
Credit: @eltociear

Let `b_k` be the number written with `k ≥ 1` digits `3`, i.e. `(10^k - 1)/3`. The decimal
concatenation of `b_k` and `2^n` is `b_k · 10^d + 2^n`, where `d` is the number of decimal digits
of `2^n`. `a(n)` (offset 0) is the least `k ≥ 1` such that the odd part of this concatenation is
prime, or `0` if there is none (`a(0) = 1`: `31`; `a(1) = 2`: `332 = 4 · 83`). The entry
conjectures:

  for all n, a(n) > 0.

`main` states that for every `n` some `k ≥ 1` makes the odd part prime. The odd part of `m` is
`m / 2 ^ m.factorization 2` (A000265).
-/

namespace OMA.S_oeis_a247342

/-- The concatenation of `k` threes followed by the decimal digits of `2 ^ n`. -/
def concat (k n : ℕ) : ℕ := (10 ^ k - 1) / 3 * 10 ^ (Nat.digits 10 (2 ^ n)).length + 2 ^ n

/-- The odd part of `m` (A000265). -/
def oddPart (m : ℕ) : ℕ := m / 2 ^ m.factorization 2

/-- The conjecture in OEIS A247342: for every `n` there is `k ≥ 1` with the odd part of the
concatenation `b_k 2^n` prime. -/
theorem main : ∀ n : ℕ, ∃ k : ℕ, 1 ≤ k ∧ (oddPart (concat k n)).Prime := by
  sorry

end OMA.S_oeis_a247342
