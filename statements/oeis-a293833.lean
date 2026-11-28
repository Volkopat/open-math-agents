import Mathlib

/-!
# A293833: Number of primes p with A020330(n) < p < A020330(n+1).

Source: https://oeis.org/A293833
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A293833 (Zhi-Wei Sun, Oct 16 2017): a(n) > 0 for all n > 0, and a(n) = 1 only for n = 12.

Conventions:
* The sequence has offset 1 (data 2, 2, 5, 3, 2, 2, 14, 4, 3, 3, 4, 1, ...).
* A020330(n) (the binary squares 3, 10, 15, 36, 45, 54, 63, 136, ...) is the number whose
  binary expansion is that of n written twice, i.e. n * (2^L + 1) where L is the number of
  binary digits of n; L is `Nat.size n` (`Nat.size 1 = 1`, `Nat.size 2 = 2`,
  `Nat.size 4 = 3`). This agrees with the Mathematica code of the entry,
  f(n) = (2^(floor(log_2 n) + 1) + 1) * n.
* `a n` is the number of primes strictly between A020330(n) and A020330(n+1).
* Both parts are stated for every n >= 1; the second part is rendered literally as an
  only-if: a(n) = 1 implies n = 12.
-/

namespace OMA.S_oeis_a293833

/-- A020330: the binary squares, n * (2^L + 1) with L the binary length of n. -/
def b (n : ℕ) : ℕ := n * (2 ^ Nat.size n + 1)

/-- A293833: number of primes p with b(n) < p < b(n+1). -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ | p.Prime ∧ b n < p ∧ p < b (n + 1)}

/-- The conjecture of Sun: a(n) > 0 for all n > 0, and a(n) = 1 only for n = 12. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n ∧ (a n = 1 → n = 12) := by
  sorry

end OMA.S_oeis_a293833
