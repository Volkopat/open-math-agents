import Mathlib

/-!
# OEIS A215066

Expansion of e.g.f. `Sum_{m >= 0} Product_{k = 1..m} (exp((2 * k - 1) * x) - 1)`:
`a(n) = Sum_{m = 0..n} Sum_{S ⊆ {1..m}} (-1)^(m - |S|) * (Sum_{k ∈ S} (2 * k - 1))^n`.

Conjectures (Peter Bala, Oct 11 2026):
1. Gauss congruences: `a(n * p^r) ≡ a(n * p^(r - 1)) [ZMOD p^r]` for all primes `p` and
   positive integers `n` and `r`.
2. Reducing `a(n)` modulo a prime `p` for `n >= 1` gives a purely periodic sequence with
   period dividing `p - 1` (`a(n + (p - 1)) ≡ a(n) [ZMOD p]`).
3. Reducing `a(n)` modulo a positive integer `k` produces an eventually periodic sequence
   with period dividing `phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a215066

/-- Contribution of `Product_{k = 1..m} (exp((2 * k - 1) * x) - 1)` at `[x^n / n!]`. -/
def w (m n : ℕ) : ℤ :=
  ∑ S ∈ (Finset.Icc 1 m).powerset,
    (-1 : ℤ) ^ (m - S.card) * (∑ k ∈ S, (2 * (k : ℤ) - 1)) ^ n

/-- Sequence A215066: `a(n) = Sum_{m = 0..n} w(m, n)`. -/
def a (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n + 1), w m n

theorem main :
    (∀ p n r : ℕ, p.Prime → 1 ≤ n → 1 ≤ r →
      a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [ZMOD (p ^ r : ℕ)]) ∧
    (∀ p n : ℕ, p.Prime → 1 ≤ n → a (n + (p - 1)) ≡ a n [ZMOD p]) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [ZMOD k]) := by
  sorry

end OMA.S_oeis_a215066
