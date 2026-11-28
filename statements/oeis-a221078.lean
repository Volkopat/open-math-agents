import Mathlib

/-!
# OEIS A221078

Expansion of e.g.f. `Sum_{m >= 0} tan(m * x)^m`:
Since `tan(x) = -i * u / (2 + u)` with `u = exp(2 * i * x) - 1`, we have
`tan(x)^m = (-i)^m * Sum_{j >= m} (-1)^(j - m) * C(j - 1, m - 1) * 2^(-j) * u^j`,
so for `m >= 1` and `n >= m` with `n ≡ m (mod 2)`:
`n! * [x^n] tan(x)^m = (-1)^((n - m) / 2) * Sum_{j = m..n} (-1)^(j - m) * C(j - 1, m - 1) * 2^(n - j) * j! * S(n, j)`,
and `a(n) = Sum_{m = 0..n} m^n * (n! * [x^n] tan(x)^m)`.
(First terms: `1, 1, 8, 164, 6400, 404176, 37541888, 4814990144, ...`)

Conjecture (Peter Bala):
Let `p` be an odd prime. The sequence `a(n) (mod p)` for `n >= 1` is purely periodic:
- If `p ≡ 1 (mod 4)`, the period divides `p - 1` (`a(n + (p - 1)) ≡ a(n) [ZMOD p]`).
- If `p ≡ 3 (mod 4)`, the period divides `2 * (p - 1)` (`a(n + 2 * (p - 1)) ≡ a(n) [ZMOD p]`).
-/

namespace OMA.S_oeis_a221078

/-- `j! * S(n, j) = Sum_{r = 0..j} (-1)^(j - r) * binomial(j, r) * r^n`. -/
def stirling2Fact (n j : ℕ) : ℤ :=
  ∑ r ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - r) * (Nat.choose j r : ℤ) * (r : ℤ) ^ n

/-- `n! * [x^n] tan(x)^m`. -/
def tanPowCoeff (m n : ℕ) : ℤ :=
  if m = 0 then (if n = 0 then 1 else 0)
  else if n < m ∨ (n - m) % 2 ≠ 0 then 0
  else
    (-1 : ℤ) ^ ((n - m) / 2) *
      ∑ j ∈ Finset.Icc m n,
        (-1 : ℤ) ^ (j - m) * (Nat.choose (j - 1) (m - 1) : ℤ) *
          2 ^ (n - j) * stirling2Fact n j

/-- Sequence A221078: `a(n) = Sum_{m = 0..n} m^n * (n! * [x^n] tan(x)^m)`. -/
def a (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n + 1), (m : ℤ) ^ n * tanPowCoeff m n

theorem main :
    (∀ p n : ℕ, p.Prime → p % 4 = 1 → 1 ≤ n → a (n + (p - 1)) ≡ a n [ZMOD p]) ∧
    (∀ p n : ℕ, p.Prime → p % 4 = 3 → 1 ≤ n → a (n + 2 * (p - 1)) ≡ a n [ZMOD p]) := by
  sorry

end OMA.S_oeis_a221078
