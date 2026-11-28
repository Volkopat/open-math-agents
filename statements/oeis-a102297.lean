import Mathlib

/-!
# A102297: Number of distinct divisors of n+1 where n and n+1 are composite or twin composite numbers.

Source: https://oeis.org/A102297
Credit: @azmiozgen

Conjecture (from the entry): 8 and 9 are the only 2 consecutive composite numbers that are both
perfect powers. Or, if x > 2, x^m + 1 != y^n for all m, n, x, y. (This is Catalan's conjecture,
proved by Mihăilescu in 2002; the entry's further relaxed variants are not stated here.)

Formalization notes:
* Perfect powers here are x^m with x ≥ 2 and m ≥ 2. The statement: if x^m + 1 = y^n with x, y ≥ 2
  and m, n ≥ 2, then x^m = 8 and y^n = 9.
-/

namespace OMA.S_oeis_a102297

/-- 8 and 9 are the only consecutive perfect powers. -/
theorem main :
    ∀ x m y n : ℕ, 2 ≤ x → 2 ≤ m → 2 ≤ y → 2 ≤ n → x ^ m + 1 = y ^ n → x ^ m = 8 ∧ y ^ n = 9 := by
  sorry

end OMA.S_oeis_a102297
