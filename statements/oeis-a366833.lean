import Mathlib

/-!
# A366833: Number of times n appears in A362965 (number of primes <= the n-th prime power).

Source: https://oeis.org/A366833
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A366833 (Paolo Xausa, Oct 25 2023): a(n) can be only 1,
2, or 3.

Conventions:
* The sequence has offset 1 (data 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, ...).
* A362965(k) is the number of primes not exceeding the k-th prime power, so a(n), the number of
  times n appears in A362965, is the number of prime powers q with pi(q) = n. Prime powers are p^j
  with p prime and j >= 1 (`IsPrimePow`); pi is `Nat.primeCounting`. For n >= 1 the set is finite
  and `Set.ncard` is its number of elements.
* The parenthetical remark of the entry about the first occurrences of the value 3 is not part of
  the statement.
-/

namespace OMA.S_oeis_a366833

/-- The conjecture recorded in A366833. -/
theorem main : ∀ n : ℕ, 0 < n →
    Set.ncard {q : ℕ | IsPrimePow q ∧ Nat.primeCounting q = n} ∈ ({1, 2, 3} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a366833
