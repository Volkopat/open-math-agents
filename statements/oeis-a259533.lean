import Mathlib

/-!
# OEIS A259533

Restricted barred preferential arrangements of an `n`-set with 3 bars,
with e.g.f. `exp(3*x) / (2 - exp(x)) = (1 + u)^3 / (1 - u)` where `u = exp(x) - 1`:
`a(n) = Sum_{j = 0..n} Stirling2(n, j) * j! * g(j)`,
where `g(0) = 1`, `g(1) = 4`, `g(2) = 7`, and `g(j) = 8` for `j >= 3`.

Conjecture (Peter Bala):
For every `k >= 1`, the sequence obtained by reducing `a(n)` modulo `k` is eventually periodic
with period dividing `phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a259533

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Coefficients of `(1 + u)^3 / (1 - u)`: `1, 4, 7, 8, 8, ...`. -/
def coeffG : ℕ → ℕ
  | 0 => 1
  | 1 => 4
  | 2 => 7
  | _ + 3 => 8

/-- Sequence A259533: `a(n) = Sum_{j = 0..n} S(n, j) * j! * coeffG(j)`. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), stirling2 n j * j.factorial * coeffG j

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a259533
