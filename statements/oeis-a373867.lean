import Mathlib

/-!
# A373867: Perfect powers of the form x^y + y^x, where x > 1 and y > 1.

Source: https://oeis.org/A373867
Credit: @azmiozgen

Conjecture (from the entry): 32 and 100 are the only terms for which x != y: 2^4 + 4^2 = 2^5 = 32 and 2^6 + 6^2 = 10^2 = 100.

Formalization notes:
* Stated as: for x, y > 1 with x < y (the expression is symmetric), x^y + y^x is a perfect power
  iff (x, y) is (2, 4) or (2, 6).
* Controls (computed): for 2 ≤ x < y < 60 the only perfect powers are at (2, 4) and (2, 6).
-/

namespace OMA.S_oeis_a373867

/-- `m` is a perfect power (A001597): `m = a^b` with `b ≥ 2` and `m ≥ 1`. -/
def IsPerfectPower (m : ℕ) : Prop := 0 < m ∧ ∃ a b : ℕ, 2 ≤ b ∧ a ^ b = m

/-- The conjecture of the entry. -/
theorem main :
    ∀ x y : ℕ, 1 < x → x < y → (IsPerfectPower (x ^ y + y ^ x) ↔ (x = 2 ∧ y = 4) ∨ (x = 2 ∧ y = 6)) := by
  sorry

end OMA.S_oeis_a373867
