import Mathlib

/-!
# A329222: Numbers m that divide 5^(m + 1) + 1.

Source: https://oeis.org/A329222
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A329222 (Juri-Stepan Gerasimov, Nov 08 2019): For k >
1, k^(m + 1) == -1 (mod m) has an infinite number of positive solutions.

Conventions:
* The sequence has offset 1 (data 1, 2, 6, 13, 14, 174, 854, 2694, 78126, 103973, 106694, 121974,
  ...).
* The congruence k^(m+1) == -1 (mod m) is stated as m dividing k^(m+1) + 1. For k = 5 this is the
  defining property of the sequence.
* The conjecture is the general statement over all bases k recorded in the entry (the sequence
  itself is one base); `infinite number of positive solutions` is `Set.Infinite` of the set of
  positive integers m satisfying the congruence.
-/

namespace OMA.S_oeis_a329222

/-- The conjecture recorded in A329222. -/
theorem main : ∀ k : ℕ, 1 < k → Set.Infinite {m : ℕ | 0 < m ∧ m ∣ k ^ (m + 1) + 1} := by
  sorry

end OMA.S_oeis_a329222
