import Mathlib

/-!
# A327468: Numbers m that divide 8^m + 7.

Source: https://oeis.org/A327468
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A327468 (Juri-Stepan Gerasimov, Oct 04 2019): For k >
1, k^m == 1-k (mod m) has an infinite number of positive solutions.

Conventions:
* The sequence has offset 1 (data 1, 3, 5, 25, 519, 290502305, 821808425, 979288025, 982989263,
  25783323897, 27771237541, 31045665345, ...).
* The congruence k^m == 1 - k (mod m) is stated as m dividing k^m + k - 1 (for k > 1 the natural
  subtraction is exact). For k = 8 this is the defining property of the sequence (m divides 8^m +
  7).
* The conjecture is the general statement over all bases k recorded in the entry (the sequence
  itself is one base); `infinite number of positive solutions` is `Set.Infinite` of the set of
  positive integers m satisfying the congruence.
-/

namespace OMA.S_oeis_a327468

/-- The conjecture recorded in A327468. -/
theorem main : ∀ k : ℕ, 1 < k → Set.Infinite {m : ℕ | 0 < m ∧ m ∣ k ^ m + k - 1} := by
  sorry

end OMA.S_oeis_a327468
