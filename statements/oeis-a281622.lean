import Mathlib

/-!
# A281622: Numbers k such that sigma(k-1) is a Mersenne prime (A000668).

Source: https://oeis.org/A281622
Credit: @azmiozgen

Conjectures (from the entry):
1. The sequence is the union of {26} and A256438.
2. The Mersenne prime 31 is the only prime p such that p = sigma(x-1) = sigma(y-1) for distinct
   numbers x and y; 31 = sigma(17-1) = sigma(26-1).

Formalization notes:
* A Mersenne prime is a prime of the form 2^q - 1. A256438 is the sequence of numbers m ≥ 2 with
  sigma(sigma(m-1)) = 2(m-1).
* Conjecture 1 is stated for every k ≥ 2: sigma(k-1) is a Mersenne prime iff k = 26 or
  sigma(sigma(k-1)) = 2(k-1). (k = 1 gives sigma(0) = 0 in Mathlib and is in neither set.)
* Conjecture 2 is stated for numbers x, y ≥ 2 (for x = 1, sigma(0) = 0 is not prime anyway).
* Controls (computed): conjecture 1 holds for 2 ≤ k < 100000; among x < 200000 the only prime
  value of sigma(x-1) taken twice is 31. The first terms 3, 5, 17, 26, 65, 4097, 65537 match.
-/

namespace OMA.S_oeis_a281622

open ArithmeticFunction

/-- Both conjectures of the entry. -/
theorem main :
    (∀ k : ℕ, 2 ≤ k →
      ((∃ q : ℕ, sigma 1 (k - 1) = 2 ^ q - 1) ∧ (sigma 1 (k - 1)).Prime ↔
        k = 26 ∨ sigma 1 (sigma 1 (k - 1)) = 2 * (k - 1))) ∧
      ∀ p : ℕ, p.Prime →
        ((∃ x y : ℕ, 2 ≤ x ∧ 2 ≤ y ∧ x ≠ y ∧ sigma 1 (x - 1) = p ∧ sigma 1 (y - 1) = p) ↔
          p = 31) := by
  sorry

end OMA.S_oeis_a281622
