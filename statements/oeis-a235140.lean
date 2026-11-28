import Mathlib

/-!
# A235140: Numerator(m*Bernoulli(m-1)+1) (mod m), for m = 1, 3, 5, 7, 9, ...

Source: https://oeis.org/A235140
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A235140 (Jonathan Sondow, Jan 07 2014): The Agoh-Giuga
Conjecture is that a(n)=0 iff 2*n+1 is 1 or a prime.

Conventions:
* The sequence has offset 0 (data 0, 0, 0, 0, 7, 0, 0, 7, 0, 0, 12, 0, ...).
* The sequence is indexed by n >= 0 with m = 2*n+1, and a(n) = numerator((2*n+1)*Bernoulli(2*n) +
  1) mod (2*n+1). Bernoulli(2*n) is the Mathlib Bernoulli number `bernoulli (2 * n)` (the two sign
  conventions for Bernoulli numbers only differ at index 1, and here the index is even). The
  numerator is `Rat.num` (of the fraction in lowest terms, an integer) and the remainder is the
  integer `%`.
-/

namespace OMA.S_oeis_a235140

/-- The conjecture recorded in A235140 (Agoh-Giuga). -/
theorem main : ∀ n : ℕ,
    ((2 * (n : ℚ) + 1) * bernoulli (2 * n) + 1).num % (2 * (n : ℤ) + 1) = 0 ↔
      (2 * n + 1 = 1 ∨ (2 * n + 1).Prime) := by
  sorry

end OMA.S_oeis_a235140
