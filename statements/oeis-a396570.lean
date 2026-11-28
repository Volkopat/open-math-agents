import Mathlib

/-!
# A396570: Numbers == 2 (mod 6) that are not the sum of two distinct upper twin primes.

Source: https://oeis.org/A396570
Credit: @keiichisince1986-bot

A396570 lists the numbers `n ≡ 2 (mod 6)` that are not the sum of two distinct upper twin primes:
`2, 8, 14, 98, 398, 404, 518, 698, 788, 908, 1118, 1148, 1268, 1358, 3248, 4208`.
The entry states: Conjecture: the sequence is finite and these are all the terms.

Conventions:
- An upper twin prime is a prime `p` such that `p - 2` is also prime (A006512: 5, 7, 13, 19, …).
  In `ℕ`, `p - 2` is truncated, but `2 - 2 = 0` and `3 - 2 = 1` are not prime, so this is exact.
- A sum of two distinct upper twin primes is `a + b` with `a ≠ b` both upper twin primes.
- The numbers `n ≡ 2 (mod 6)` are `2, 8, 14, …` (A016933).
- Finite with these as all the terms means that the data list every term, so the conjecture says
  that the set of such `n` is exactly the set of the 16 numbers above.
-/

namespace OMA.S_oeis_a396570

/-- `p` is an upper twin prime: `p` and `p - 2` are both prime. -/
def IsUpperTwinPrime (p : ℕ) : Prop :=
  p.Prime ∧ (p - 2).Prime

theorem main :
    {n : ℕ | n % 6 = 2 ∧
        ¬ ∃ a b : ℕ, IsUpperTwinPrime a ∧ IsUpperTwinPrime b ∧ a ≠ b ∧ n = a + b} =
      {2, 8, 14, 98, 398, 404, 518, 698, 788, 908, 1118, 1148, 1268, 1358, 3248, 4208} := by
  sorry

end OMA.S_oeis_a396570
