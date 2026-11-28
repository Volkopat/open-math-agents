import Mathlib

/-!
# Howroyd's conjecture for Hardin's singly defective permutations with one maximum

Source: https://oeis.org/A183264 (R. H. Hardin, 2011; conjecture by Andrew Howroyd, 2020).
Credit: @frido22
-/

namespace OMA.S_oeis_a183264

/-- Words with the given multiset of letters and one maximal plateau. The two
sides are weakly increasing and weakly decreasing and can be empty. -/
def peakWords {α : Type*} [LinearOrder α] (M : α) (content : Multiset α) : Set (List α) :=
  {w | (w : Multiset α) = content ∧ ∃ (up down : Multiset α) (k : ℕ),
    (∀ x ∈ up, x < M) ∧ (∀ x ∈ down, x < M) ∧
    w = up.sort (· ≤ ·) ++ List.replicate (k + 1) M ++ down.sort (· ≥ ·)}

/-- Count the words on the surviving alphabet, repeating exactly one of its letters. -/
noncomputable def countRepeats {α : Type*} [LinearOrder α] (s : Finset α) : ℕ :=
  if h : s.Nonempty then ∑ r ∈ s, (peakWords (s.max' h) (r ::ₘ s.val)).ncard else 0

/-- Omit one letter from the ordered alphabet of size `n`. Each word uniquely
identifies its omitted and repeated letters. -/
noncomputable def a (n : ℕ) : ℕ := ∑ m : Fin n, countRepeats (Finset.univ.erase m)

/-- The integer exponent gives Howroyd's formula its usual meaning also at `n = 2`. -/
theorem main : ∀ n : ℕ, 1 < n →
    (a n : ℚ) = (n : ℚ) * (3 * (n : ℚ) - 4) * (2 : ℚ) ^ ((n : ℤ) - 3) := by
  sorry

end OMA.S_oeis_a183264
