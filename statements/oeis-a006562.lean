import Mathlib

/-!
# A006562: Balanced primes

Source: https://oeis.org/A006562
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Balanced primes (of order one) are primes that are the average of the previous and the
following prime: `5, 53, 157, 173, …`. Conjecture (Alain Rocchelli, OEIS, 2024):
`lim_{n → ∞} n · (log a(n))² / a(n) = 1/2`.

## Encoding

* `p` is balanced if `p = prime(k)` for some `k ≥ 1` (0-indexed `Nat.nth Nat.Prime`) with
  `2 · prime(k) = prime(k - 1) + prime(k + 1)`.
* `a n` is the `n`-th balanced prime with OEIS offset `1`: `a n = Nat.nth IsBalanced (n - 1)`.
* Only the first of the two conjectures in the entry is stated here.
-/

namespace OMA.S_oeis_a006562

open Filter Topology

/-- `p` is a balanced prime. -/
def IsBalanced (p : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ p = Nat.nth Nat.Prime k ∧
    2 * Nat.nth Nat.Prime k = Nat.nth Nat.Prime (k - 1) + Nat.nth Nat.Prime (k + 1)

/-- `a n`: the `n`-th balanced prime (offset `1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsBalanced (n - 1)

theorem main :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.log (a n) ^ 2 / a n) atTop (𝓝 (1 / 2)) := by
  sorry

end OMA.S_oeis_a006562
