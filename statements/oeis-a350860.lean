import Mathlib

/-!
# A350860: Number of ways to write n as w^4 + (x^4 + y^2 + z^2)/81 with w,x,y,z nonnegative, y <= z

Source: https://oeis.org/A350860
Credit: @niclorusso

Conjecture 1 (Zhi-Wei Sun, in the comments of A350860): a(n) > 0 for any nonnegative integer n.

(Conjecture 1 continues "Also, every n = 0,1,2,... can be written as 4*w^4 + (x^4 + y^2 + z^2)/81
with w,x,y,z integers", and the entry has Conjectures 2 and 3; only a(n) > 0 is formalized here.)

Conventions:
* w, x, y, z are nonnegative integers. Writing n = w^4 + (x^4 + y^2 + z^2)/81 means that the
  quotient is exact, i.e. 81 * n = 81 * w^4 + x^4 + y^2 + z^2.
* The condition y <= z only avoids counting a representation twice; it does not affect whether a
  representation exists, so it is dropped.
-/

namespace OMA.S_oeis_a350860

/-- Sun's Conjecture 1 on A350860 (first part): every `n >= 0` is `w^4 + (x^4 + y^2 + z^2)/81`
with nonnegative integers `w, x, y, z`. -/
theorem main : ∀ n : ℕ, ∃ w x y z : ℕ, 81 * n = 81 * w ^ 4 + x ^ 4 + y ^ 2 + z ^ 2 := by
  sorry

end OMA.S_oeis_a350860
