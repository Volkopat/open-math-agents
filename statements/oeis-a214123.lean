import Mathlib

/-!
# A214123: Smallest positive k such that n+k(n-1) is prime

Source: https://oeis.org/A214123
Credit: @xor2k

The entry's text is a remark that mentions the twin prime conjecture: a(n) is 1 when 2n-1 is
prime, which is equivalent to a((p+1)/2)=1 for prime p > 2, therefore there are an infinite
number of pairs of consecutive 1s in the sequence if the twin prime conjecture is true.

Formalized claim (the twin prime conjecture itself is not formalized, only used as a hypothesis):
1. for every `n ≥ 2` with `2n - 1` prime, `a(n) = 1`;
2. for every prime `p > 2`, `a((p + 1)/2) = 1`;
3. if there are infinitely many primes `p` with `p + 2` prime, then there are infinitely many
   `n ≥ 2` with `a(n) = 1` and `a(n + 1) = 1` (a pair of consecutive 1s).

Conventions:
- Offset 2: the sequence is defined for `n ≥ 2` (for `n = 1` the value `1 + k * 0 = 1` is never
  prime). `a n` is `sInf` of the set of positive `k` with `n + k * (n - 1)` prime; for `n ≥ 2` this
  set is nonempty (Dirichlet), so `sInf` is its least element.
- `2 * n - 1` and `n - 1` are natural subtraction (exact for `n ≥ 2`); `(p + 1) / 2` is natural
  division (exact for odd `p`).
- The twin prime conjecture is stated as the infinitude of `{p | p prime and p + 2 prime}`.
-/

namespace OMA.S_oeis_a214123

/-- Smallest positive `k` such that `n + k(n-1)` is prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ (n + k * (n - 1)).Prime}

/-- The three claims of the remark in A214123. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n → (2 * n - 1).Prime → a n = 1) ∧
    (∀ p : ℕ, p.Prime → 2 < p → a ((p + 1) / 2) = 1) ∧
    ({p : ℕ | p.Prime ∧ (p + 2).Prime}.Infinite →
      {n : ℕ | 2 ≤ n ∧ a n = 1 ∧ a (n + 1) = 1}.Infinite) := by
  sorry

end OMA.S_oeis_a214123
