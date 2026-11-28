import Mathlib

/-!
# A214922: Numbers of the form x^2 + y^2 + z^3 + w^3 (x, y, z, w >= 0).

Source: https://oeis.org/A214922
Credit: @darealpandaboi

Conjecture: 23 is the only number not in this sequence.

Translation notes.
* n is in the sequence when n = x^2 + y^2 + z^3 + w^3 with x, y, z, w >= 0 (n >= 0, offset 1
  with a(1) = 0). The statement says the set of n not of this form is exactly {23}.
* A computer check finds 23 as the only exception up to 200000.
-/

namespace OMA.S_oeis_a214922

theorem main :
    {n : ℕ | ¬ ∃ x y z w : ℕ, n = x ^ 2 + y ^ 2 + z ^ 3 + w ^ 3} = {23} := by
  sorry

end OMA.S_oeis_a214922
