import Mathlib

/-!
# OEIS A179929

`a(n) = 2^n * A(n, -1/2)` (e.g.f. `3 / (1 + 2 * exp(-3*x))`):
`a(n) = Sum_{j = 0..n} (-1)^(n + j) * 3^(n - j) * 2^j * Stirling2(n, j) * j!`.

Conjecture (Peter Bala):
For every `k >= 1`, the sequence `a(n) (mod k)` is eventually periodic with period dividing
`phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a179929

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Sequence A179929: `a(n) = Sum_{j = 0..n} (-1)^(n + j) * 3^(n - j) * 2^j * S(n, j) * j!`. -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (n + j) * (3 : ℤ) ^ (n - j) * (2 : ℤ) ^ j * (stirling2 n j * j.factorial : ℤ)

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [ZMOD k] := by
  sorry

end OMA.S_oeis_a179929
