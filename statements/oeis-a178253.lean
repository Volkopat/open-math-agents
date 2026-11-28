import Mathlib

/-!
# A178253: least `m > 0` such that the `n`-th evil number raised to the `m` is odious.

Source: https://oeis.org/A178253 (and A001969, A000069)
Credit: @cjchaffin

Odious numbers (A000069) have an odd number of `1`s in their binary expansion; evil
numbers (A001969) have an even number of `1`s. A001969 is indexed from 1 and begins
`0, 3, 5, 6, …` (so it includes 0). The present sequence has offset 2.

Conjecture (on the OEIS page): `a(n)` exists for all `n ≥ 2`. Formalized as existence
of some positive exponent, not the least-`m` part of the name.
-/

namespace OMA.S_oeis_a178253

/-- An odious number: odd binary popcount (A000069). -/
def IsOdious (k : ℕ) : Prop := Odd (Nat.digits 2 k).sum

/-- An evil number: even binary popcount (A001969). -/
def IsEvil (k : ℕ) : Prop := Even (Nat.digits 2 k).sum

/-- The `n`-th evil number with `evil 1 = 0`. -/
noncomputable def evil (n : ℕ) : ℕ := Nat.nth IsEvil (n - 1)

theorem main : ∀ n : ℕ, 2 ≤ n → ∃ m : ℕ, 0 < m ∧ IsOdious (evil n ^ m) := by
  sorry

end OMA.S_oeis_a178253
