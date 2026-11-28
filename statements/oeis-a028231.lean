import Mathlib

/-!
# OEIS A028231: from the hexagons in a circle problem

Source: https://oeis.org/A028231
Credit: @adamghaida (agent: grok-bot)

A028231 is 1, 22, 313, 4366, 60817, ... (offset 0). Its OEIS comments describe it as the numbers
`k` such that `(k^2 + k + 1)/3` is a square (Arkadiusz Wesolowski, Feb 10 2012).

Conjecture (Colin Barker, Apr 10 2012): `a(n) = 15*a(n-1) - 15*a(n-2) + a(n-3)`.

Formalization notes:
* The sequence is defined here through Wesolowski's characterization: `a n` is the `n`-th
  (0-indexed, increasing) natural number `k` for which `k^2 + k + 1` is divisible by 3 and the
  quotient is a perfect square. (`(k^2 + k + 1)/3` being a square means in particular that it is
  an integer, hence the divisibility condition.) With this convention `a 0 = 1`, `a 1 = 22`.
* The recurrence holds for every `n ≥ 3` in OEIS indexing; here it is stated, shifted, for every
  `n : ℕ` as `a (n + 3) = 15 * a (n + 2) - 15 * a (n + 1) + a n`, computed in `ℤ`.
-/

namespace OMA.S_oeis_a028231

/-- `k` is a term: `(k^2 + k + 1)/3` is (an integer and) a perfect square. -/
def IsTerm (k : ℕ) : Prop :=
  3 ∣ k ^ 2 + k + 1 ∧ IsSquare ((k ^ 2 + k + 1) / 3)

/-- `a n`: the `n`-th term (0-indexed) of A028231. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm n

theorem main : ∀ n : ℕ,
    (a (n + 3) : ℤ) = 15 * (a (n + 2) : ℤ) - 15 * (a (n + 1) : ℤ) + (a n : ℤ) := by
  sorry

end OMA.S_oeis_a028231
