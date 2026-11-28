import Mathlib

/-!
# A154285: Number of ordered triples <p,s,t> satisfying p+L_s+L_t=n, where p is an odd prime, s and t are nonnegative and the Lucas number L_s or L_t is odd.

Source: https://oeis.org/A154285
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun): a(n) > 0 for all n = 5, 6, ...; in other words, any integer n > 4 can be
represented as the sum of an odd prime, an odd Lucas number and a Lucas number. (Further
conjectures of the entry, for powers of Lucas numbers and on lim inf a(n)/log(n), are not stated
here.)

Formalization notes:
* L_s is the s-th Lucas number (L_0 = 2, L_1 = 1), defined below.
* a(n) > 0 means n has at least one representation, so the conjecture is stated as the existence
  of a representation.
* Controls (computed): every n with 5 ≤ n < 3000 has a representation.
-/

namespace OMA.S_oeis_a154285

/-- The Lucas numbers `L(0) = 2, L(1) = 1, L(n+2) = L(n+1) + L(n)`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 5 ≤ n → ∃ p s t : ℕ, p.Prime ∧ Odd p ∧ (Odd (lucas s) ∨ Odd (lucas t)) ∧
      p + lucas s + lucas t = n := by
  sorry

end OMA.S_oeis_a154285
