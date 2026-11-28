import Mathlib

/-!
# A182003: alternating sums of consecutive primes (Sun)

Source: https://oeis.org/A182003
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Zhi-Wei Sun, 2012, listed in A182003): `a(n)` always exists and does not exceed
`2.2 n` for `n > 1`, where `a(n)` is the least prime `p_k` such that
`n = p_k - p_{k-1} + ⋯ + (-1)^{k-j} p_j` for some `1 ≤ j ≤ k` (`p_k` the `k`-th prime).

Conventions:
* Primes are indexed from `1`: `p_k = Nat.nth Nat.Prime (k - 1)`.
* "Exists and does not exceed `2.2 n`": for every `n > 1` there are `1 ≤ j ≤ k` with
  `p_k ≤ 2.2 n` and the alternating sum equal to `n` (then the least such `p_k` is `≤ 2.2 n`).
-/

namespace OMA.S_oeis_a182003

/-- The `k`-th prime, `k ≥ 1`. -/
noncomputable def p (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- `p_k - p_{k-1} + ⋯ + (-1)^{k-j} p_j`. -/
noncomputable def altSum (j k : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc j k, (-1 : ℤ) ^ (k - i) * (p i : ℤ)

theorem main :
    ∀ n : ℕ, 1 < n → ∃ j k : ℕ, 1 ≤ j ∧ j ≤ k ∧ altSum j k = n ∧ (p k : ℝ) ≤ 2.2 * n := by
  sorry

end OMA.S_oeis_a182003
