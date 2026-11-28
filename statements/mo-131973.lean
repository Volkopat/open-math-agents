import Mathlib

/-!
# Distinctive property of the primes 17 and 19?

Source: https://mathoverflow.net/questions/131973/distinctive-property-of-the-primes-17-and-19
Credit: @shc261392

Question. Is it true that a prime number `p` divides `1^1 + 2^2 + 3^3 + ⋯ + (p-1)^{p-1}` if and
only if `p ∈ {17, 19}`?

Reading used here: the claim exactly as asked. (Heuristically one expects about `ln ln n` such
primes below `n`, so the expected answer is no; no example other than 17 and 19 is known, and a
search finds none below `3 · 10^4`.)
-/

namespace OMA.S_mo_131973

theorem main :
    ∀ p : ℕ, p.Prime → (p ∣ ∑ k ∈ Finset.Ico 1 p, k ^ k ↔ p = 17 ∨ p = 19) := by
  sorry

end OMA.S_mo_131973
