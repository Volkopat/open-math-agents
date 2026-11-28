import Mathlib

/-!
# A289682: Catalan numbers read modulo 16.

Source: https://oeis.org/A289682
Credit: @rickmanelius

Conjecture (Robert Israel, Jul 09 2017): a(2^n-1) = 13 and a(2^n) = 6 for n >= 3.
(Jianing Song, Apr 15 2026: The conjecture is correct. For the first part, see A178854 for more
details; for the second part, simply note that Catalan(n+1)/Catalan(n) = 2*(2*n+1)/(n+2), and so
in particular Catalan(2^k)/Catalan(2^k-1) == -2 (mod 2^k).)

Formalization notes:
* Offset 0, with `a n = catalan n % 16`, where `catalan` is Mathlib's Catalan number
  (catalan 0 = 1, catalan 1 = 1, catalan 2 = 2, catalan 3 = 5, catalan 4 = 14, ..., A000108).
  The data begin 1, 1, 2, 5, 14, 10, 4, 13, 6, 14, ..., matching the entry.
* The conjecture is the conjunction of both congruences, claimed for every n ≥ 3 (the same n in
  both parts). For n ≥ 3 we have 2^n ≥ 8, so the natural-number subtraction 2^n - 1 is the usual
  one.
-/

namespace OMA.S_oeis_a289682

/-- a(n) = Catalan(n) mod 16. -/
def a (n : ℕ) : ℕ := catalan n % 16

theorem main : ∀ n : ℕ, 3 ≤ n → a (2 ^ n - 1) = 13 ∧ a (2 ^ n) = 6 := by
  sorry

end OMA.S_oeis_a289682
