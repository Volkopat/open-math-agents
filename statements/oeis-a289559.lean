import Mathlib

/-!
# A289559: sums of two fourth powers modulo a prime

Source: https://oeis.org/A289559 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A289559, offset 1: Number of modulo n residues among sums of two fourth powers. Data
1, 2, 3, 3, 3, 6, 7, 3, 7, 6, 11, 9, 10, 14, 9, 3, 13, 14, 19, 9, 21, 22, 23, 9, 11, 20, 19, 21, ...

Comments: Conjecture: the only primes p for which a(p) < p are 5, 13, 17, 29. - Robert Israel,
Jul 09 2017. (A later comment of the entry says that the conjecture is true and points to a
MathOverflow answer.)

Formalization notes.
* `a n` is the number of the residues c in `ZMod n` of the form x^4 + y^4 with x, y in
  `ZMod n` (`Nat.card` of the subtype).
* The data agree: a(5) = 3, a(13) = 10, a(17) = 13, a(29) = 22, and a(p) = p for the other
  primes p of the data.
-/

namespace OMA.S_oeis_a289559

/-- A289559(n): the number of residues modulo n that are a sum of two fourth powers. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {c : ZMod n // ∃ x y : ZMod n, x ^ 4 + y ^ 4 = c}

/-- Israel's conjecture: the only primes p with a(p) < p are 5, 13, 17 and 29. -/
theorem main : ∀ p : ℕ, p.Prime → (a p < p ↔ p = 5 ∨ p = 13 ∨ p = 17 ∨ p = 29) := by
  sorry

end OMA.S_oeis_a289559
