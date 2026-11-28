import Mathlib

/-!
# A274605: Numbers k such that there is no prime between the k-th perfect power and the (k+1)-st perfect power.

Source: https://oeis.org/A274605
Credit: @azmiozgen

Conjecture (from the entry): 23268 is the last term of the sequence.

Formalization notes:
* The perfect powers are A001597 = 1, 4, 8, 9, 16, ...; the k-th one (k ≥ 1) is
  `Nat.nth IsPerfectPower (k - 1)`. "No prime between" means no prime strictly between.
* Stated as: 23268 is a term and no k > 23268 is a term.
* Controls (computed, perfect powers ≤ 10^9): the terms are 3, 6, 8, 14, 60, 72, 216, 328, 361,
  23268, as in the entry.
-/

namespace OMA.S_oeis_a274605

/-- `m` is a perfect power (A001597): `m = a^b` with `b ≥ 2` and `m ≥ 1`. -/
def IsPerfectPower (m : ℕ) : Prop := 0 < m ∧ ∃ a b : ℕ, 2 ≤ b ∧ a ^ b = m

/-- The `k`-th perfect power, `pp 1 = 1`. -/
noncomputable def pp (k : ℕ) : ℕ := Nat.nth IsPerfectPower (k - 1)

/-- `k` is a term: no prime lies strictly between the `k`-th and `(k+1)`-st perfect powers. -/
def IsTerm (k : ℕ) : Prop := ¬ ∃ q : ℕ, q.Prime ∧ pp k < q ∧ q < pp (k + 1)

/-- The conjecture of the entry. -/
theorem main :
    IsTerm 23268 ∧ ∀ k : ℕ, 23268 < k → ¬ IsTerm k := by
  sorry

end OMA.S_oeis_a274605
