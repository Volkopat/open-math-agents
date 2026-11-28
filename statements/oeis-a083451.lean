import Mathlib

/-!
# A083451: (n concatenated n times) - n^n.

Source: https://oeis.org/A083451
Credit: @bnb9001

The sequence has offset 1 (for instance a(4) = 4444 - 4^4 = 4188). The concatenation of `n`
with itself `n` times, in base 10, is the number whose decimal digits are those of `n` repeated
`n` times; with Mathlib's little-endian `Nat.digits`, it is
`Nat.ofDigits 10 (List.flatten (List.replicate n (Nat.digits 10 n)))`.

Conjecture (Amarnath Murthy): all terms are positive for n > 1. The entry notes that this is
true.
-/

namespace OMA.S_oeis_a083451

/-- The base-10 concatenation of `n` with itself `n` times. -/
def concatRep (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (List.flatten (List.replicate n (Nat.digits 10 n)))

/-- For every `n > 1`, `(n concatenated n times) - n ^ n > 0`. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < (concatRep n : ℤ) - (n : ℤ) ^ n := by
  sorry

end OMA.S_oeis_a083451
