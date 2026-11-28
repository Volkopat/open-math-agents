import Mathlib

/-!
# OEIS A052895

Expansion of e.g.f. `C(exp(x) - 1) = (1 / (2 * (exp(x) - 1))) * (1 - sqrt(5 - 4 * exp(x)))`,
where `C(x) = Sum_{j >= 0} catalan(j) * x^j` is the o.g.f. of the Catalan numbers:
`a(n) = Sum_{j = 0..n} Stirling2(n, j) * j! * catalan(j)`.

Conjecture (Peter Bala, Jan 15 2018):
For every `k >= 1`, the sequence obtained by reducing `a(n)` modulo `k` is eventually periodic
with period dividing `phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a052895

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Sequence A052895: `a(n) = Sum_{j = 0..n} S(n, j) * j! * catalan(j)`. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), stirling2 n j * j.factorial * catalan j

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a052895
