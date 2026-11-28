import Mathlib

/-!
# A089758: Primes arising in A089757

Source: https://oeis.org/A089758

Conjecture (OEIS A089758):
The greedy sequence A089757 of strictly increasing positive multiples of `3` such
that the base-10 concatenation `a(n) || a(n - 1) || ... || a(1) || 1` is prime
(generating the primes of A089758) is infinite.

Conventions:
- First terms of A089757 (0-indexed here): `3, 6, 9, 12, 27, 30, ...`.
- Corresponding primes of A089758: `31, 631, 9631, 129631, 27129631, 3027129631, ...`.
- `chainVal a n` builds `a(n - 1) || ... || a(0) || 1` recursively from `chainVal a 0 = 1`.
-/

namespace OMA.S_oeis_a089758

/-- Base-10 concatenation `u || v` for `v ≥ 1`. -/
def concat10 (u v : ℕ) : ℕ :=
  u * 10 ^ (Nat.digits 10 v).length + v

/-- Concatenation `a(n - 1) || ... || a(0) || 1` for a sequence `a : ℕ → ℕ`. -/
def chainVal (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => concat10 (a n) (chainVal a n)

/-- Conjecture: the greedy sequence A089757 (and hence the prime sequence A089758) is
infinite, i.e., a next strictly larger multiple of `3` yielding a prime concatenation
exists at every step. -/
theorem main :
    ∃ a : ℕ → ℕ,
      ∀ n : ℕ,
        IsLeast
          {m : ℕ | 0 < m ∧ 3 ∣ m ∧ (∀ i < n, a i < m) ∧ Nat.Prime (concat10 m (chainVal a n))}
          (a n) := by
  sorry

end OMA.S_oeis_a089758
