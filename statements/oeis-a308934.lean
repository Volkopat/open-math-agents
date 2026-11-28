import Mathlib

/-!
# A308934: Number of ways to write n as (2^a*3^b)^2 + (2^c*3^d)^2 + x^2 + 2*y^2, where a,b,c,d,x,y are nonnegative integers with 2^a*3^b >= 2^c*3^d.

Source: https://oeis.org/A308934
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry; verified for n up to 2*10^9 and 10^9):
1. a(n) > 0 for all n > 1.
2. Any integer n > 1 can be written as (2^a*3^b)^2 + (2^c*5^d)^2 + x^2 + 2*y^2 with a, b, c, d, x, y
   nonnegative integers.

Formalization notes:
* a(n) > 0 is stated as the existence of a representation (the ordering 2^a 3^b ≥ 2^c 3^d does not
  affect existence).
* Controls (computed): both conjectures hold for 1 < n < 20000.
-/

namespace OMA.S_oeis_a308934



/-- The conjectures of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 1 < n → ∃ a b c d x y : ℕ,
        (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 3 ^ d) ^ 2 + x ^ 2 + 2 * y ^ 2 = n) ∧
      ∀ n : ℕ, 1 < n → ∃ a b c d x y : ℕ,
        (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + 2 * y ^ 2 = n := by
  sorry

end OMA.S_oeis_a308934
