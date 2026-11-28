import Mathlib

/-!
# On the set `{n > 0 : n is a quadratic nonresidue modulo the n-th prime}`

Source: https://mathoverflow.net/questions/352195 (Zhi-Wei Sun, CC BY-SA 4.0).

Let `S` be the set of positive integers `n` such that `n` is a quadratic nonresidue modulo the
`n`-th prime `p_n`. Its first elements are 2, 3, 6, 7, 8, 10, 11, 13, 15, 18, … (OEIS A332021).
Conjecture: `S` has asymptotic density `1/2`, i.e.
`lim_{N → ∞} |{n ∈ S : n ≤ N}| / N = 1/2`.
(The asker also suggests the stronger `|{n ∈ S : n ≤ x}| = x/2 + O(√x)`, and asks whether `S` is
infinite; neither is stated here.)

Formalization notes:
* `p_n` is the `n`-th prime with `p_1 = 2`, i.e. `Nat.nth Nat.Prime (n - 1)`.
* "`n` is a quadratic nonresidue modulo `p_n`" is `¬ IsSquare (n : ZMod p_n)`. Since `n < p_n`, the
  class of `n` is nonzero; for `n = 1` (modulus `2`) `1` is a square, so `1 ∉ S`, matching the
  data above.
* Checked numerically: the proportion up to `N` is `0.502`, `0.4995`, `0.497` for
  `N = 10^3, 10^4, 1.7·10^4`.
-/

namespace OMA.S_mo_352195

open Filter Topology

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- The positive integers `n` that are quadratic nonresidues modulo the `n`-th prime. -/
def S : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ ¬ IsSquare ((n : ZMod (prime n)))}

/-- Sun's conjecture: `S` has asymptotic density `1/2`. -/
theorem main :
    Tendsto (fun N : ℕ => ((S ∩ Set.Icc 1 N).ncard : ℝ) / N) atTop (𝓝 (1 / 2)) := by
  sorry

end OMA.S_mo_352195
