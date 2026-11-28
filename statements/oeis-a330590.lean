import Mathlib

/-!
# A330590: number of positive integers m dividing x^n - x^k for all integers x

Source: https://oeis.org/A330590 (conjecture in the formula section of the entry)

Entry (offset 2): triangle read by rows, T(n,k) is the number of positive integers m dividing
x^n - x^k for all integers x, 0 < k < n.
Conjecture: T(n,1) = 2^A067513(n-1).

Conventions:
* `T n k` is the number of elements (`Set.ncard`) of the set of positive integers `m` with
  `m ∣ x^n - x^k` for every integer `x` (this set is finite for 0 < k < n, being contained in
  the divisors of 2^n - 2^k).
* `A067513 n` is the number of divisors `d` of `n` such that `d + 1` is prime (the title of
  A067513).
* The conjecture concerns the first column k = 1, whose rows start at n = 2.
-/

namespace OMA.S_oeis_a330590

/-- T(n,k): the number of positive integers m dividing x^n - x^k for all integers x. -/
noncomputable def T (n k : ℕ) : ℕ := Set.ncard {m : ℕ | 0 < m ∧ ∀ x : ℤ, (m : ℤ) ∣ x ^ n - x ^ k}

/-- A067513(n): the number of divisors d of n such that d + 1 is prime. -/
def A067513 (n : ℕ) : ℕ := ((Nat.divisors n).filter fun d => (d + 1).Prime).card

theorem main : ∀ n : ℕ, 2 ≤ n → T n 1 = 2 ^ A067513 (n - 1) := by
  sorry

end OMA.S_oeis_a330590
