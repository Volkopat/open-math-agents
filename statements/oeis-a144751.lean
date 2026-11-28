import Mathlib

/-!
# A144751: Mathar's conjectured generating function is wrong

Source: https://oeis.org/A144751
Credit: @sntntHb

A144751 (offset 1): a(1) = 3, a(n + 1) = 1 + a(n) + least odd prime factor of a(n);
data 3, 7, 15, 19, 39, 43, 87, 91, 99, 103, 207, 211, 423, ...

The entry records (R. J. Mathar, Jun 16 2009) that the conjectured g.f.
(-4x^11 + 12x^10 + 8x^9 + 24x^8 + 56x^7 + 72x^6 + 43x^5 + 39x^4 + 19x^3 + 15x^2 + 7x + 3)
/ (4x^12 - 5x^6 + 1) is wrong: it matches only an initial segment of the sequence.

Formalization: the least odd prime factor of `m` is the least prime factor of the odd part
`m / 2 ^ (m.factorization 2)`. The g.f. (indexed from x^0 = a(1)) has a numerator of degree 11
and denominator 1 - 5x^6 + 4x^12, so it is the g.f. of the sequence if and only if the twelve
initial terms agree (they do) and a(n) = 5 a(n-6) - 4 a(n-12) for every n ≥ 13. `main` states
that this recurrence fails for some n ≥ 13, that is, that the conjectured g.f. is wrong.
-/

namespace OMA.S_oeis_a144751

/-- The least odd prime factor of `m`: the least prime factor of the odd part of `m`. -/
noncomputable def lopf (m : ℕ) : ℕ := Nat.minFac (m / 2 ^ (m.factorization 2))

/-- `b n = a (n + 1)`: b 0 = 3, b (n + 1) = 1 + b n + lopf (b n). -/
noncomputable def b : ℕ → ℕ
  | 0 => 3
  | n + 1 => 1 + b n + lopf (b n)

/-- A144751 with offset 1. -/
noncomputable def a (n : ℕ) : ℕ := b (n - 1)

/-- The conjectured g.f. is wrong: its recurrence a(n) = 5a(n-6) - 4a(n-12) fails for some n ≥ 13. -/
theorem main : ¬ ∀ n : ℕ, 13 ≤ n → (a n : ℤ) = 5 * a (n - 6) - 4 * a (n - 12) := by
  sorry

end OMA.S_oeis_a144751
