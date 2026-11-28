import Mathlib

/-!
# OEIS A301921

Expansion of e.g.f. `1 / (1 - u / (1 - u^2 / (1 - u^3 / ...)))` where `u = exp(x) - 1`:
`a(n) = Sum_{j = 0..n} Stirling2(n, j) * j! * A005169(j)`,
where `A005169(j) = F(1, j)` is the coefficient `[u^j]` of the continued fraction
`F_m(u) = 1 / (1 - u^m * F_{m+1}(u)) = 1 + u^m * F_{m+1}(u) * F_m(u)`.

Conjecture (Peter Bala, Aug 19 2025):
For every `k >= 1`, the sequence obtained by reducing `a(n)` modulo `k` is eventually periodic
with period dividing `phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a301921

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Coefficients `[u^r] F_m(u)` of `F_m(u) = 1 / (1 - u^m * F_{m+1}(u))` (for `m >= 1`). -/
def cfCoeff (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 =>
    if h : m = 0 ∨ r + 1 < m then 0
    else ∑ i ∈ Finset.range (r + 1 - m + 1),
      cfCoeff (m + 1) (r + 1 - m - i) * cfCoeff m (min i (r + 1 - m))
termination_by r => r
decreasing_by
  all_goals omega

/-- Sequence A301921: `a(n) = Sum_{j = 0..n} S(n, j) * j! * A005169(j)`. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), stirling2 n j * j.factorial * cfCoeff 1 j

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a301921
