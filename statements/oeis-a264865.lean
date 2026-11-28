import Mathlib

/-!
# A264865: Primes of the form 2^x + y (x >= 0 and 0 <= y < 2^x) such that all the numbers 2^(x-a) + (y+a) (0 < a <= x) are composite.

Source: https://oeis.org/A264865
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A264865): The sequence has infinitely many terms.

Conventions: `x` and `y` are natural numbers with `y < 2^x`, so `x ≥ 0` and `0 ≤ y < 2^x` as in
the source. For `0 < a ≤ x` the subtraction `x - a` in `ℕ` is exact. A number `n` is composite
when `1 < n` and `n` is not prime. The sequence lists the primes `p` that have such a
representation `p = 2^x + y` with all of the numbers `2^(x-a) + (y+a)`, `0 < a ≤ x`, composite;
the conjecture says that this set is infinite.
-/

namespace OMA.S_oeis_a264865

/-- The terms of A264865. -/
def S : Set ℕ :=
  {p : ℕ | p.Prime ∧ ∃ x y : ℕ, y < 2 ^ x ∧ p = 2 ^ x + y ∧
    ∀ a : ℕ, 0 < a → a ≤ x → 1 < 2 ^ (x - a) + (y + a) ∧ ¬ (2 ^ (x - a) + (y + a)).Prime}

/-- Sun's conjecture: A264865 has infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a264865
