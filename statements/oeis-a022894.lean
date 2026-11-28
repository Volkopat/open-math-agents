import Mathlib

/-!
# OEIS A022894: signed prime sums, growth rate 4

Source: https://oeis.org/A022894
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of solutions of `c(1) prime(1) + ⋯ + c(2n+1) prime(2n+1) = 0` with
`c(1) = 1` and `c(i) = ±1` for `i > 1`. Conjecture (in the entry): `lim a(n)^{1/n} = 4`.

Encoding: `prime(i)` is `Nat.nth Nat.Prime (i - 1)`; sign choices for `i = 2, …, 2n+1` are
maps `Fin (2n) → Bool` (`true` = `+1`), position `j` carrying `prime(j + 2)`.
-/

namespace OMA.S_oeis_a022894

open Filter

/-- The `i`-th prime, `i ≥ 1`. -/
noncomputable def prime (i : ℕ) : ℤ := (Nat.nth Nat.Prime (i - 1) : ℤ)

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun c : Fin (2 * n) → Bool =>
    prime 1 + ∑ j : Fin (2 * n), (if c j then 1 else -1) * prime (j + 2) = 0).card

/-- The conjecture `a(n)^{1/n} → 4`. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / n)) atTop (nhds 4) := by
  sorry

end OMA.S_oeis_a022894
