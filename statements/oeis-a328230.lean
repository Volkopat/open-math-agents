import Mathlib

/-!
# A328230: Numbers m that divide 3^(m + 1) + 1.

Source: https://oeis.org/A328230
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A328230 (Juri-Stepan Gerasimov, Oct 08 2019): For k >
2, k^(m + 1) == -1 (mod m) has an infinite number of positive solutions.

Conventions:
* The sequence has offset 1 (data 1, 2, 4, 5, 14, 244, 365, 434, 854, 2294, 3794, 5966, ...).
* The congruence k^(m+1) == -1 (mod m) is stated as m dividing k^(m+1) + 1. For k = 3 this is the
  defining property of the sequence.
* The conjecture is the general statement over all bases k recorded in the entry (the sequence
  itself is one base); `infinite number of positive solutions` is `Set.Infinite` of the set of
  positive integers m satisfying the congruence.
-/

namespace OMA.S_oeis_a328230

/-- The conjecture recorded in A328230. -/
theorem main : ∀ k : ℕ, 2 < k → Set.Infinite {m : ℕ | 0 < m ∧ m ∣ k ^ (m + 1) + 1} := by
  sorry

end OMA.S_oeis_a328230
