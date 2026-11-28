import Mathlib

/-!
# OEIS A258899

Expansion of e.g.f. `2 - exp(2) + Sum_{m >= 1} 2^m * exp(x^m) / m!`:
For `n >= 1`, `a(n) = Sum_{m ∣ n} 2^m * n! / (m! * (n / m)!)`, with `a(0) = 1`.
(First terms: `1, 2, 6, 10, 42, 34, 786, 130, 17058, ...`)

Conjecture (Peter Bala):
For every positive integer `k`, the sequence `a(n) (mod k)` is eventually periodic with
period dividing `phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a258899

/-- Sequence A258899: `a(0) = 1` and for `n >= 1`,
`a(n) = Sum_{m ∣ n} 2^m * (n! / (m! * (n / m)!))`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    ∑ m ∈ (n + 1).divisors,
      2 ^ m * ((n + 1).factorial / (m.factorial * ((n + 1) / m).factorial))

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a258899
