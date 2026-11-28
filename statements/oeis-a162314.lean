import Mathlib

/-!
# OEIS A162314

Row sums of A162313, with e.g.f. `exp(2*x) / (2 - exp(2*x))`:
`a(n) = 2^n * Sum_{j = 0..n} Stirling2(n, j) * j! * (if j = 0 then 1 else 2)`.

Conjecture (Peter Bala):
For every `k >= 1`, the sequence `a(n) (mod k)` is eventually periodic with period dividing
`phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a162314

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Sequence A162314: `a(n) = 2^n * Sum_{j = 0..n} S(n, j) * j! * (if j = 0 then 1 else 2)`. -/
def a (n : ℕ) : ℕ :=
  2 ^ n * ∑ j ∈ Finset.range (n + 1), stirling2 n j * j.factorial * (if j = 0 then 1 else 2)

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a162314
