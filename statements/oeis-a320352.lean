import Mathlib

/-!
# OEIS A320352

Expansion of e.g.f. `(exp(x) - 1) / (exp(x) - exp(2*x) + 1)`:
`a(n) = Sum_{j = 0..n} Stirling2(n, j) * j! * Fibonacci(j)`.

Conjecture (Peter Bala, Aug 19 2025):
For every `k >= 1`, the sequence obtained by reducing `a(n)` modulo `k` is eventually periodic
with period dividing `phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a320352

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Sequence A320352: `a(n) = Sum_{j = 0..n} S(n, j) * j! * Nat.fib j`. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), stirling2 n j * j.factorial * Nat.fib j

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a320352
