import Mathlib

/-!
# OEIS A316144

Expansion of e.g.f. `Product_{k >= 1} ((1 + (exp(x) - 1)^k) / (1 - (exp(x) - 1)^k))^2`:
`a(n) = Sum_{j = 0..n} Stirling2(n, j) * j! * over2(j)`,
where `over2(j)` is the coefficient `[u^j] Product_{k >= 1} ((1 + u^k) / (1 - u^k))^2`
(2-colored overpartitions of `j`).

Conjecture (Peter Bala):
For every `k >= 1`, the sequence obtained by reducing `a(n)` modulo `k` is eventually periodic
with period dividing `phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a316144

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Overpartitions of `r`: `[u^r] Product_{k >= 1} (1 + u^k) / (1 - u^k)`. -/
noncomputable def overpart (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (r + 1),
    (Nat.Partition.distincts i).card * Fintype.card (Nat.Partition (r - i))

/-- 2-colored overpartitions of `j`: `[u^j] Product_{k >= 1} ((1 + u^k) / (1 - u^k))^2`. -/
noncomputable def over2 (j : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (j + 1), overpart r * overpart (j - r)

/-- Sequence A316144: `a(n) = Sum_{j = 0..n} S(n, j) * j! * over2(j)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), stirling2 n j * j.factorial * over2 j

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a316144
