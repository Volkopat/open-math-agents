import Mathlib

/-!
# MO 225929: primes among floors of powers

Source: https://mathoverflow.net/questions/225929

Mills proved that for some real c the floors of c^(3^n) are all prime.  The question
asks whether some real d has all floors of d^n prime.  Since floor(d^0) = 1 is not
prime, the standard reading (also used in the linked MO question) is n >= 1; this is
recorded in the comment.  Only the body of `main` is `sorry`.
-/

namespace OMA.S_mo_225929

theorem main : ∃ d : ℝ, ∀ n : ℕ, 1 ≤ n → Nat.Prime ⌊d ^ n⌋₊ := by
  sorry

end OMA.S_mo_225929
