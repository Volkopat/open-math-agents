import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Twin primes with the smaller prime congruent to 3 modulo 4

Source: Jon Aycock, MathOverflow question 441440.
https://mathoverflow.net/questions/441440/are-there-infinitely-many-twin-primes-p-and-p2-with-p1-divisible-by-4

The title asks whether infinitely many twin-prime pairs p, p + 2 satisfy
the divisibility condition 4 ∣ p + 1. Each pair is indexed by its smaller prime.
-/

namespace OMA.S_mo_441440

theorem main :
    {p : ℕ | p.Prime ∧ (p + 2).Prime ∧ 4 ∣ p + 1}.Infinite := by
  sorry

end OMA.S_mo_441440
