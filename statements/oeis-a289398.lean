import Mathlib

/-!
# OEIS A289398

`a(n)` is the least integer `m > n` such that `(n^2 + m^2) / 2` is a square.

Conjecture (Robert Israel, Jul 07 2017):
For any `n ≥ 1`, `a(n) = 7 * n` if and only if all prime factors of `n` are in A042999
(i.e. `p = 2` or `p ≡ 3, 5 (mod 8)`).
-/

namespace OMA.S_oeis_a289398

/-- Predicate: `m > n` and `(n^2 + m^2) / 2` is a perfect square. -/
def IsValid (n m : ℕ) : Prop :=
  n < m ∧ ∃ k : ℕ, n ^ 2 + m ^ 2 = 2 * k ^ 2

/-- `a(n)` is the least integer `m > n` such that `(n^2 + m^2) / 2` is a square. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | IsValid n m }

/-- A042999: primes `p` such that `p = 2` or `p % 8 = 3` or `p % 8 = 5`. -/
def InA042999 (p : ℕ) : Prop :=
  p.Prime ∧ (p = 2 ∨ p % 8 = 3 ∨ p % 8 = 5)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n = 7 * n ↔ ∀ p : ℕ, p.Prime → p ∣ n → InA042999 p) := by
  sorry

end OMA.S_oeis_a289398
