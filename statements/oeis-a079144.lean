import Mathlib

/-!
# OEIS A079144

Number of labeled interval orders on `n` elements (`(2+2)`-free posets), with e.g.f.
`Sum_{m >= 0} Product_{j = 1..m} (1 - exp(-j * x))`:
`a(n) = Sum_{m = 0..n} Sum_{S ⊆ {1..m}} (-1)^|S| * (-Sum_{j ∈ S} j)^n`.

Conjectures (Peter Bala, Dec 26 2021):
1. For every `k >= 1`, reducing `a(n)` modulo `k` gives an eventually periodic sequence
   with period dividing `phi(k) = Nat.totient k`.
2. For every shift `i >= 0`, prime `p`, and positive integers `n` and `r`,
   the Gauss congruence `a(n * p^r + i) ≡ a(n * p^(r - 1) + i) [ZMOD p^r]` holds.
-/

namespace OMA.S_oeis_a079144

/-- Contribution of the `m`-th product `Product_{j = 1..m} (1 - exp(-j * x))` at `[x^n / n!]`. -/
def w (m n : ℕ) : ℤ :=
  ∑ S ∈ (Finset.Icc 1 m).powerset,
    (-1 : ℤ) ^ S.card * (-(∑ j ∈ S, (j : ℤ))) ^ n

/-- Sequence A079144: number of labeled interval orders on `n` elements. -/
def a (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n + 1), w m n

theorem main :
    (∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [ZMOD k]) ∧
    (∀ i p n r : ℕ, p.Prime → 1 ≤ n → 1 ≤ r →
      a (n * p ^ r + i) ≡ a (n * p ^ (r - 1) + i) [ZMOD (p ^ r : ℕ)]) := by
  sorry

end OMA.S_oeis_a079144
