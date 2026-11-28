import Mathlib

/-!
# OEIS A306082

Expansion of e.g.f. `Product_{k >= 1} 1 / (1 - (exp(x) - 1)^(k^2))`:
`a(n) = Sum_{j = 0..n} Stirling2(n, j) * j! * pSq(j)`,
where `pSq(j)` counts integer partitions of `j` into perfect squares.

Conjecture (Peter Bala):
For every `k >= 1`, the sequence obtained by reducing `a(n)` modulo `k` is eventually periodic
with period dividing `phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a306082

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Number of partitions of `j` into perfect squares: `[u^j] Product_{k >= 1} 1 / (1 - u^(k^2))`. -/
noncomputable def pSq (j : ℕ) : ℕ :=
  Nat.card { p : Nat.Partition j // ∀ x ∈ p.parts, ∃ r : ℕ, x = r ^ 2 }

/-- Sequence A306082: `a(n) = Sum_{j = 0..n} S(n, j) * j! * pSq(j)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), stirling2 n j * j.factorial * pSq j

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a306082
