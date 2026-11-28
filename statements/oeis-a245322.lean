import Mathlib

/-!
# OEIS A245322

Expansion of e.g.f. `Sum_{m >= 0} sin(m * x)^m`:
Since `sin(m * x)^m = (-i)^m * sinh(i * m * x)^m` and `n! * [x^n] sinh(x)^m = m! * partOdd(n, m)`
vanishes unless `n ≡ m (mod 2)`, we have
`a(n) = Sum_{m = 0..n} (-1)^((n - m) / 2) * m^n * m! * partOdd(n, m)`.

Conjectures (Peter Bala):
1. For `n >= 1`, `a(2 * n)` is even and `a(2 * n - 1)` is odd.
2. For every prime `p ≡ 1 (mod 4)`, `a(n) (mod p)` for `n >= 1` is purely periodic with period
   dividing `p - 1` (`a(n + (p - 1)) ≡ a(n) [ZMOD p]`).
3. For every prime `p ≡ 3 (mod 4)`, `a(n) (mod p)` for `n >= 1` is purely periodic with period
   dividing `2 * (p - 1)` (`a(n + 2 * (p - 1)) ≡ a(n) [ZMOD p]`).
-/

namespace OMA.S_oeis_a245322

/-- Number of partitions of an `n`-element set into `m` blocks of odd size. -/
def partOdd : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, m + 1 => ∑ j ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * j) * partOdd (n - 2 * j) m
termination_by n _ => n
decreasing_by omega

/-- Sequence A245322: `a(n) = Sum_{m = 0..n} (-1)^((n - m) / 2) * m^n * m! * partOdd(n, m)`. -/
def a (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ ((n - m) / 2) * ((m ^ n * m.factorial * partOdd n m : ℕ) : ℤ)

theorem main :
    (∀ n : ℕ, 1 ≤ n → Even (a (2 * n)) ∧ Odd (a (2 * n - 1))) ∧
    (∀ p n : ℕ, p.Prime → p % 4 = 1 → 1 ≤ n → a (n + (p - 1)) ≡ a n [ZMOD p]) ∧
    (∀ p n : ℕ, p.Prime → p % 4 = 3 → 1 ≤ n → a (n + 2 * (p - 1)) ≡ a n [ZMOD p]) := by
  sorry

end OMA.S_oeis_a245322
