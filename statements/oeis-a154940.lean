import Mathlib

/-!
# A154940: Number of ways to express n as the sum of an odd prime, a Lucas number and a Catalan number.

Source: https://oeis.org/A154940
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, Jan 16 2009): a(n) > 0 for n = 5, 6, ... (Sun's further guess about
lim inf a(n)/log(n) is not stated here.)

Formalization notes:
* Lucas numbers L_s (s ≥ 0, L_0 = 2, L_1 = 1) are defined below; Catalan numbers are Mathlib's
  `catalan t` (t ≥ 0).
* a(n) > 0 means n has at least one representation, so the conjecture is stated as the existence
  of a representation.
* Controls (computed): every n with 5 ≤ n < 3000 has a representation.
-/

namespace OMA.S_oeis_a154940

/-- The Lucas numbers `L(0) = 2, L(1) = 1, L(n+2) = L(n+1) + L(n)`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 5 ≤ n → ∃ p s t : ℕ, p.Prime ∧ Odd p ∧ p + lucas s + catalan t = n := by
  sorry

end OMA.S_oeis_a154940
