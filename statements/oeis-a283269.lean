import Mathlib

/-!
# A283269: Number of ways to write n as x^2 + y^2 + z^2 with x,y,z integers such that x + 3*y + 5*z is a square.

Source: https://oeis.org/A283269
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(2^k*m) > 0 for any positive odd integers k and m. Also, a(4*n+1) = 0 only for n = 63.
(ii) For any positive odd integers k and m, we can write 2^k*m as x^2 + y^2 + z^2 with x, y, z integers
such that x + 3*y + 5*z is twice a square.
(iii) For any positive odd integer n not congruent to 7 modulo 8, we can write n as x^2 + y^2 + z^2 with
x, y, z integers such that x + 3*y + 4*z is a square.

Formalization notes:
* Variables are integers; "a square" is s^2 and "twice a square" 2 s^2 for an integer s.
* a(N) > 0 is the existence of a representation; "a(4n+1) = 0 only for n = 63" is stated as: 4n + 1
  has no representation iff n = 63.
* Controls (computed): (i), (ii) hold for 2^k m < 4000 (k, m odd); a(4n+1) = 0 for n < 1000 only at
  n = 63; (iii) holds for odd n < 4000.
-/

namespace OMA.S_oeis_a283269

/-- `N = x² + y² + z²` with `x + 3y + 5z` a square. -/
def Rep (N : ℕ) : Prop := ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = N ∧ IsSquare (x + 3 * y + 5 * z)

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ k m : ℕ, Odd k → Odd m → Rep (2 ^ k * m)) ∧
      (∀ n : ℕ, ¬ Rep (4 * n + 1) ↔ n = 63) ∧
      (∀ k m : ℕ, Odd k → Odd m → ∃ x y z s : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 2 ^ k * m ∧
        x + 3 * y + 5 * z = 2 * s ^ 2) ∧
      ∀ n : ℕ, Odd n → n % 8 ≠ 7 → ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n ∧ IsSquare (x + 3 * y + 4 * z) := by
  sorry

end OMA.S_oeis_a283269
