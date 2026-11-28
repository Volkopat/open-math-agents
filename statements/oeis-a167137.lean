import Mathlib

/-!
# OEIS A167137

Expansion of e.g.f. `P(exp(x) - 1)`, where `P(x) = Sum_{j >= 0} p(j) * x^j` is the generating
function of the integer partition numbers `p(j) = Fintype.card (Nat.Partition j)` (A000041):
`a(n) = Sum_{j = 0..n} p(j) * j! * S(n, j)`.
(First terms: `1, 1, 5, 31, 257, 2551, 30065, ...`)

Conjectures (Peter Bala):
1. For every positive integer `k`, the sequence `a(n) (mod k)` is eventually periodic with
   period dividing `phi(k) = Nat.totient k`.
2. More generally, the same eventual periodicity modulo `k` with period dividing `phi(k)` holds
   for any integer sequence with e.g.f. `G(exp(x) - 1)`, where `G(x) = Sum_{j >= 0} g(j) * x^j`
   is an integral power series (`g : ℕ → ℤ`).
-/

namespace OMA.S_oeis_a167137

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Sequence A167137: `a(n) = Sum_{j = 0..n} p(j) * j! * S(n, j)`. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), Fintype.card (Nat.Partition j) * j.factorial * stirling2 n j

/-- General e.g.f. coefficient of `G(exp(x) - 1)` for an integral series `G(x) = Sum g(j) x^j`. -/
def evalG (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), g j * (j.factorial : ℤ) * (stirling2 n j : ℤ)

theorem main :
    (∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k]) ∧
    (∀ (g : ℕ → ℤ) (k : ℕ), 1 ≤ k →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → evalG g (n + Nat.totient k) ≡ evalG g n [ZMOD k]) := by
  sorry

end OMA.S_oeis_a167137
