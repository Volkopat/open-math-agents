import Mathlib

/-!
# OEIS A355409

Expansion of e.g.f. `1 / (1 + exp(2*x) - exp(3*x)) = 1 / (1 - u - 2*u^2 - u^3)` where `u = exp(x) - 1`:
`a(n) = Sum_{j = 0..n} Stirling2(n, j) * j! * g(j)`,
where `g(0) = 1`, `g(1) = 1`, `g(2) = 3`, `g(j + 3) = g(j + 2) + 2 * g(j + 1) + g(j)`.

Conjecture (Peter Bala):
For every `k >= 1`, the sequence obtained by reducing `a(n)` modulo `k` is eventually periodic
with period dividing `phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a355409

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Coefficients of `1 / (1 - u - 2*u^2 - u^3)`. -/
def coeffG : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | j + 3 => coeffG (j + 2) + 2 * coeffG (j + 1) + coeffG j

/-- Sequence A355409: `a(n) = Sum_{j = 0..n} S(n, j) * j! * coeffG(j)`. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), stirling2 n j * j.factorial * coeffG j

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a355409
