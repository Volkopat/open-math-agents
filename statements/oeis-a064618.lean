import Mathlib

/-!
# OEIS A064618

Stirling transform of `(n!)^2`:
`a(n) = Sum_{j = 0..n} Stirling2(n, j) * (j!)^2`.

Conjecture (Peter Bala):
For every `k >= 1`, the sequence `a(n) (mod k)` is eventually periodic with period dividing
`phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a064618

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Sequence A064618: `a(n) = Sum_{j = 0..n} S(n, j) * (j!)^2`. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), stirling2 n j * j.factorial ^ 2

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a064618
