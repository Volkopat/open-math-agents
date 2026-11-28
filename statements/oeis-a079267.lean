import Mathlib

/-!
# OEIS A079267: short pairs in perfect matchings are asymptotically Poisson(1)

Source: https://oeis.org/A079267
`d(n, s)` is the number of perfect matchings of `{1, …, 2n}` with exactly `s` short pairs
(pairs `{i, i+1}`). Conjecture: asymptotically the `n`-th row has a Poisson distribution with
mean `1`, i.e. for each `s`, `d(n, s) / (2n-1)!! → e⁻¹ / s!`.

Conventions. A perfect matching of `Fin (2n)` is a fixed-point-free involution `m`; it has
`(2n-1)!!` elements in total, and the row is normalised by that total.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a079267

open Filter Topology Real

/-- Perfect matchings of `Fin (2n)` (fixed-point-free involutions) with exactly `s` short
pairs `{i, i+1}`. -/
def d (n s : ℕ) : ℕ :=
  (Finset.univ.filter fun m : Equiv.Perm (Fin (2 * n)) =>
    (∀ i, m i ≠ i) ∧ (∀ i, m (m i) = i) ∧
    (Finset.univ.filter fun i : Fin (2 * n) => (m i).val = i.val + 1).card = s).card

theorem main :
    ∀ s : ℕ, Tendsto (fun n : ℕ => (d n s : ℝ) / (Nat.doubleFactorial (2 * n - 1) : ℝ))
      atTop (𝓝 (exp (-1) / s.factorial)) := by
  sorry

end OMA.S_oeis_a079267
