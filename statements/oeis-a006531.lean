import Mathlib

/-!
# OEIS A006531: periodicity of labeled semiorder counts modulo k

Source: https://oeis.org/A006531
`a n` is the number of semiorders on `n` labeled elements; by the formula on the entry
(Bala), `a n = ∑_{k=0}^{n} (-1)^(n+k) Catalan(k) k! S(n, k)`. Conjecture (Bala): for each
`k ≥ 1` the sequence `a n mod k` is eventually periodic with exact period dividing `φ(k)`.

Conventions. `a` is defined by Bala's formula (with Mathlib's `catalan` and the
Stirling numbers `stirling2` defined below). The minimal period of an eventually periodic sequence divides every period,
so "exact period dividing `φ k`" is stated as: some period `T ∣ φ k` works from some point on.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a006531

/-- Stirling numbers of the second kind. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- A006531 via Bala's formula. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1) ^ (n + k) * ((catalan k * k.factorial * stirling2 n k : ℕ) : ℤ)

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ T N : ℕ, 0 < T ∧ T ∣ k.totient ∧
      ∀ n ≥ N, a (n + T) ≡ a n [ZMOD k] := by
  sorry

end OMA.S_oeis_a006531
