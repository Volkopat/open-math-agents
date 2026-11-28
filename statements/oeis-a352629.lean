import Mathlib

/-!
# A352629: Number of ways to write n as a^2 + 2*b^2 + c^4 + 9*c^4 + 3*c^2*d^2, where a,b,c,d are nonnegative integers.

Source: https://oeis.org/A352629
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 for all n = 0, 1, 2, .... In other words, any
nonnegative integer can be written as a^2 + 2*b^2 + c^4 + 9*d^4 + 3*c^2*d^2 with a, b, c, d
integers. (The remark "it seems that a(n) = 1 only for n = 0, 5, 6, ..." is not stated here.)

Formalization notes:
* The name prints "c^4 + 9*c^4"; the conjecture's own wording and the term 3*c^2*d^2 show that the
  form is a^2 + 2b^2 + c^4 + 9d^4 + 3c^2d^2, which is stated. All exponents are even, so integers
  and nonnegative integers give the same values; ℕ is used.
* Controls (computed): every n < 20000 is represented.
-/

namespace OMA.S_oeis_a352629



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, ∃ a b c d : ℕ, a ^ 2 + 2 * b ^ 2 + c ^ 4 + 9 * d ^ 4 + 3 * c ^ 2 * d ^ 2 = n := by
  sorry

end OMA.S_oeis_a352629
