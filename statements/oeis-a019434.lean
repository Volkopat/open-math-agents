import Mathlib

/-!
# Fermat primes

Source: https://oeis.org/A019434
Credit: @Ciphore

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a019434

/-- The Fermat-prime conjecture: the only indices giving primes `2^(2^k) + 1` are
`k = 0, 1, 2, 3, 4`. -/
theorem main : {k : ℕ | (2 ^ (2 ^ k) + 1).Prime} = ({0, 1, 2, 3, 4} : Set ℕ) := by
  sorry

end OMA.S_oeis_a019434
