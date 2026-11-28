import Mathlib

/-!
# OEIS A305550

Expansion of e.g.f. `Product_{k >= 1} (1 + (exp(x) - 1)^k)`:
`a(n) = Sum_{j = 0..n} Stirling2(n, j) * j! * q(j)`,
where `q(j) = (Nat.Partition.distincts j).card` counts partitions of `j` into distinct parts.

Conjecture (Peter Bala, Jul 08 2022):
For every `k >= 1`, the sequence obtained by reducing `a(n)` modulo `k` is eventually periodic
with period dividing `phi(k) = Nat.totient k`.
-/

namespace OMA.S_oeis_a305550

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Sequence A305550: `a(n) = Sum_{j = 0..n} S(n, j) * j! * q(j)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), stirling2 n j * j.factorial * (Nat.Partition.distincts j).card

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + Nat.totient k) ≡ a n [MOD k] := by
  sorry

end OMA.S_oeis_a305550
