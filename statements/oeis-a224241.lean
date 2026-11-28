import Mathlib

/-!
# A224241: Numbers k such that k^2 XOR (k+1)^2 is a square, and k^2 XOR (k+2)^2 is also a square, where XOR is the bitwise logical exclusive-or operator.

Source: https://oeis.org/A224241
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A224241 (Alex Ratushnyak, Apr 01 2013): the sequence is
infinite.

Conventions:
* The sequence has offset 1 (data 0, 3, 130456, 342096, 1226720, 291575011, 379894587, 523040160,
  15216609776, 136622606520, ...).
* XOR is the bitwise exclusive-or of natural numbers, `Nat.xor` (notation `^^^`); `a square` is
  `IsSquare` (0 included). k ranges over the natural numbers (the first term is 0).
* `The sequence is infinite` / `has infinitely many terms` is rendered as `Set.Infinite` of the
  set of all numbers with the defining property of the OEIS name.
-/

namespace OMA.S_oeis_a224241

/-- The conjecture recorded in A224241. -/
theorem main : Set.Infinite {k : ℕ | IsSquare ((k ^ 2) ^^^ ((k + 1) ^ 2)) ∧
    IsSquare ((k ^ 2) ^^^ ((k + 2) ^ 2))} := by
  sorry

end OMA.S_oeis_a224241
