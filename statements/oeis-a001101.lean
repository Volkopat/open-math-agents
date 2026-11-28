import Mathlib

/-!
# A001101: Moran numbers

Source: https://oeis.org/A001101
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Moran numbers are the `k` such that `k / (sum of digits of k)` is prime: `18, 21, 27, 42, …`.
Witno conjectures that `a(n) ~ c · n · log(n)²` for some `c`.

## Encoding

* `k ≥ 1` is a Moran number if its decimal digit sum `s` divides `k` and `k / s` is prime.
* `a n` is the `n`-th Moran number with offset `1`: `Nat.nth IsMoran (n - 1)`.
* "`a(n) ~ c n log(n)²` for some `c`" is read with `c > 0`:
  `a(n) / (n log(n)²) → c`.
-/

namespace OMA.S_oeis_a001101

open Filter Topology

/-- `k` is a Moran number. -/
def IsMoran (k : ℕ) : Prop :=
  1 ≤ k ∧ (Nat.digits 10 k).sum ∣ k ∧ (k / (Nat.digits 10 k).sum).Prime

/-- `a n`: the `n`-th Moran number (offset `1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsMoran (n - 1)

theorem main :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (a n : ℝ) / (n * Real.log n ^ 2)) atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a001101
