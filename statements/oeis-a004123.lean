import Mathlib

/-!
# OEIS A004123

Number of generalized weak orders on `n` points:
`a(n) = Sum_{j = 0..n} Stirling2(n, j) * j! * 2^j`, e.g.f. `1 / (3 - 2 * exp(x))`.

Conjectures (Peter Bala, Jul 08 2022):
1. For every `k >= 1`, `a(n) mod k` is eventually periodic with period dividing `phi(k)`
   (i.e. `∃ N, ∀ n >= N, a(n + phi(k)) ≡ a(n) [MOD k]`).
2. More generally, for any integer sequence `g : ℕ → ℤ`, the sequence
   `b(n) = n! * [x^n] G(exp(x) - 1) = Sum_{j = 0..n} Stirling2(n, j) * j! * g(j)`
   is eventually periodic modulo `k` with period dividing `phi(k)`.
-/

namespace OMA.S_oeis_a004123

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Sequence A004123: `a(n) = Sum_{j = 0..n} S(n, j) * j! * 2^j`. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), stirling2 n j * j.factorial * 2 ^ j

/-- General sequence `n! * [x^n] G(exp(x) - 1)` for `G(x) = Sum_{j >= 0} g(j) * x^j`. -/
def genSeq (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), (stirling2 n j * j.factorial : ℤ) * g j

theorem main :
    (∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k]) ∧
    (∀ (g : ℕ → ℤ) (k : ℕ), 1 ≤ k →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → genSeq g (n + Nat.totient k) ≡ genSeq g n [ZMOD k]) := by
  sorry

end OMA.S_oeis_a004123
